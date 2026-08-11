#!/usr/bin/env python3
"""Generate a Lean proof with a local model and accept it only after Lean verifies it."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TEMPLATE = ROOT / "AI_Proof_Demo" / "PartialProof.lean.template"
DEFAULT_COMPLETION = ROOT / "AI_Proof_Demo" / "completion.txt"
DEFAULT_OUTPUT = ROOT / "AI_Proof_Demo" / "AIProofGenerated.lean"
DEFAULT_CONTEXT = ROOT / "AI_Proof_Demo" / "FiniteDiffProofReference.txt"
DEFAULT_DEEPSEEK_TASK = ROOT / "AI_Proof_Demo" / "DeepSeekLocalGoal.lean.template"
DEFAULT_CONFIG = ROOT / "AI_Proof_Demo" / "config.json"
DEFAULT_OLLAMA_URL = "http://127.0.0.1:11434"
DEFAULT_MODEL = "hf.co/unsloth/DeepSeek-Prover-V2-7B-GGUF:BF16"
DEFAULT_TRANSFORMERS_MODEL = "deepseek-ai/DeepSeek-Prover-V2-7B"
DEFAULT_THINK = "false"
DEFAULT_LOG_DIR = ROOT / "AI_Proof_Demo" / "runs"
DEFAULT_GPU_MEMORY_GIB = 8.0
DEEPSEEK_MODEL_FRAGMENT = "deepseek-prover"
COMPLETION_BEGIN = "-- AI_COMPLETION_BEGIN"
COMPLETION_END = "-- AI_COMPLETION_END"
HOLE_PATTERN = re.compile(
    r"^(?P<indent>[ \t]*)-- AI_PROOF_HOLE[ \t]*$", re.MULTILINE
)
FORBIDDEN_PATTERN = re.compile(r"\b(?:sorry|admit|axiom)\b", re.IGNORECASE)
TOP_LEVEL_COMMAND_PATTERN = re.compile(
    r"^[ \t]*(?:import|namespace|section|end|theorem|lemma|def|example|"
    r"instance|class|structure|inductive)\b",
    re.IGNORECASE | re.MULTILINE,
)
SIMPLE_SIMP_PATTERN = re.compile(
    r"^(?P<command>simp(?:_all)?(?:\s+only)?)\s*\["
    r"(?P<arguments>[A-Za-z_][A-Za-z0-9_'.]*(?:\s*,\s*"
    r"[A-Za-z_][A-Za-z0-9_'.]*)*)\]\s*$"
)
UNUSED_SIMP_ARGUMENT_PATTERN = re.compile(
    r"This simp argument is unused:\s*\n\s+(?P<argument>[^\n]+)"
)
CONFIG_PATH_KEYS = {
    "template",
    "deepseek_task",
    "completion",
    "output",
    "transformers_cache",
    "log_dir",
}
CONFIG_PATH_LIST_KEYS = {"context"}
CONFIG_STRING_LIST_KEYS = {"forbid_identifier", "instruction"}
CONFIG_STRING_KEYS = {
    "backend",
    "device",
    "model",
    "ollama_url",
    "prompt_mode",
    "think",
    "keep_alive",
}
CONFIG_INTEGER_KEYS = {
    "attempts",
    "num_predict",
    "prefill_num_predict",
    "num_ctx",
    "generation_timeout",
    "timeout",
}
CONFIG_NUMBER_KEYS = {"temperature", "gpu_memory_gib"}
CONFIG_BOOLEAN_KEYS = {"json_schema", "verify_only", "no_log", "offline"}
CONFIG_ALLOWED_KEYS = (
    CONFIG_PATH_KEYS
    | CONFIG_PATH_LIST_KEYS
    | CONFIG_STRING_LIST_KEYS
    | CONFIG_STRING_KEYS
    | CONFIG_INTEGER_KEYS
    | CONFIG_NUMBER_KEYS
    | CONFIG_BOOLEAN_KEYS
    | {"schema_version"}
)


class ProofError(RuntimeError):
    """An expected proof-generation or verification failure."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def elapsed_seconds(start: float) -> float:
    return round(time.perf_counter() - start, 3)


def write_json_atomic(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".tmp",
            prefix=path.name + ".",
            dir=path.parent,
            delete=False,
        ) as temporary:
            json.dump(data, temporary, ensure_ascii=False, indent=2)
            temporary.write("\n")
            temporary_path = Path(temporary.name)
        os.replace(temporary_path, path)
        temporary_path = None
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


class RunLogger:
    """Persist one queryable JSON record for a complete generation run."""

    def __init__(
        self,
        args: argparse.Namespace,
        argv: Sequence[str],
        enabled: bool,
    ) -> None:
        self.started_perf = time.perf_counter()
        started_at = utc_now()
        compact_time = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        safe_model = re.sub(r"[^A-Za-z0-9_.-]+", "_", args.model)
        self.path = (
            args.log_dir.resolve()
            / f"{compact_time}_{safe_model}_{os.getpid()}.json"
            if enabled
            else None
        )
        self.record: dict[str, Any] = {
            "schema_version": 1,
            "started_at": started_at,
            "finished_at": None,
            "duration_seconds": None,
            "status": "running",
            "exit_code": None,
            "argv": list(argv),
            "configuration": {
                "config": relative_to_root(args.config),
                "mode": "verify_only" if args.verify_only else "generate",
                "offline": args.offline,
                "backend": args.backend,
                "device": args.device,
                "gpu_memory_gib": args.gpu_memory_gib,
                "model": args.model,
                "prompt_mode": args.prompt_mode,
                "ollama_url": args.ollama_url,
                "template": relative_to_root(args.template),
                "deepseek_task": relative_to_root(args.deepseek_task),
                "transformers_cache": relative_to_root(args.transformers_cache),
                "completion": relative_to_root(args.completion),
                "output": relative_to_root(args.output),
                "contexts": [relative_to_root(path) for path in (args.context or [])],
                "attempts": args.attempts,
                "temperature": args.temperature,
                "think": args.think,
                "num_predict": args.num_predict,
                "prefill_num_predict": args.prefill_num_predict,
                "num_ctx": args.num_ctx,
                "generation_timeout_seconds": args.generation_timeout,
                "lean_timeout_seconds": args.timeout,
                "json_schema": args.json_schema,
                "keep_alive": args.keep_alive,
                "forbidden_identifiers": args.forbid_identifier,
                "instructions": args.instruction,
            },
            "inputs": {},
            "prompt": {},
            "attempts": [],
        }
        self.save()

    def save(self) -> None:
        if self.path is not None:
            write_json_atomic(self.path, self.record)

    def start_attempt(self, attempt: dict[str, Any]) -> None:
        self.record["attempts"].append(attempt)
        self.save()

    def finish_attempt(self, attempt: dict[str, Any], started_perf: float) -> None:
        attempt["finished_at"] = utc_now()
        attempt["duration_seconds"] = elapsed_seconds(started_perf)
        self.save()
        print(
            "Attempt {attempt} finished: status={status}, generation={generation:.3f}s, "
            "verification={verification:.3f}s, total={total:.3f}s".format(
                attempt=attempt["attempt"],
                status=attempt["status"],
                generation=attempt.get("generation_seconds", 0.0),
                verification=attempt.get("verification_seconds", 0.0),
                total=attempt["duration_seconds"],
            ),
            flush=True,
        )

    def finish(self, status: str, exit_code: int, error: str | None = None) -> None:
        self.record["finished_at"] = utc_now()
        self.record["duration_seconds"] = elapsed_seconds(self.started_perf)
        self.record["status"] = status
        self.record["exit_code"] = exit_code
        if error is not None:
            self.record["error"] = error
        self.save()
        if self.path is not None:
            print(f"Run log: {relative_to_root(self.path)}")


def read_text(path: Path, description: str) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as error:
        raise ProofError(f"Could not read {description} {path}: {error}") from error


def normalize_completion(raw: str) -> str:
    """Extract tactic text from JSON/fenced/plain model output."""
    text = raw.strip()
    if not text:
        raise ProofError("Ollama returned an empty completion.")

    parsed = None
    for candidate in (text, extract_json_object(text)):
        if candidate is None:
            continue
        try:
            parsed = json.loads(candidate)
            break
        except json.JSONDecodeError:
            parsed = None
    loose_proof = None if parsed is not None else extract_loose_proof_value(text)
    if isinstance(parsed, dict) and isinstance(parsed.get("proof"), str):
        text = parsed["proof"].strip()
    elif (
        isinstance(parsed, dict)
        and isinstance(parsed.get("proof"), list)
        and all(isinstance(line, str) for line in parsed["proof"])
    ):
        text = "\n".join(parsed["proof"]).strip()
    elif loose_proof is not None:
        text = loose_proof.strip()

    fenced = re.search(r"```(?:lean4?|text)?\s*\n(.*?)```", text, re.DOTALL | re.IGNORECASE)
    if fenced:
        text = fenced.group(1).strip()

    text = textwrap.dedent(text).strip()
    lines = text.splitlines()
    if lines and lines[0].strip() == "by":
        text = textwrap.dedent("\n".join(lines[1:])).strip()

    if not text:
        raise ProofError("The extracted Lean completion is empty.")
    forbidden = FORBIDDEN_PATTERN.search(text)
    if forbidden:
        raise ProofError(
            f"Completion contains forbidden Lean keyword: {forbidden.group(0)}"
        )
    top_level_command = TOP_LEVEL_COMMAND_PATTERN.search(text)
    if top_level_command:
        command = top_level_command.group(0).strip().split()[0]
        raise ProofError(
            f"Completion contains a top-level Lean command instead of tactics: {command}"
        )
    if "AI_PROOF_HOLE" in text:
        raise ProofError("Completion must not contain the proof-hole marker.")
    return text


def extract_deepseek_completion(raw: str) -> str:
    """Extract tactics from DeepSeek-Prover's final Lean code block."""
    blocks = re.findall(
        r"```(?:lean4?|text)?\s*\n(.*?)```", raw, re.DOTALL | re.IGNORECASE
    )
    text = blocks[-1].strip() if blocks else raw.strip()

    if COMPLETION_BEGIN in text and COMPLETION_END in text:
        text = text.split(COMPLETION_BEGIN, 1)[1].split(COMPLETION_END, 1)[0]
        return normalize_completion(text)

    proof_match = re.search(r":=\s*by\s*\n(?P<body>.*)", text, re.DOTALL)
    if proof_match is not None:
        body = proof_match.group("body")
        body = re.split(r"^\s*end(?:\s+\S+)?\s*$", body, maxsplit=1, flags=re.MULTILINE)[0]
        body = "\n".join(
            line
            for line in body.splitlines()
            if line.strip() not in {COMPLETION_BEGIN, COMPLETION_END}
        )
        return normalize_completion(body)

    return normalize_completion(text)


def extract_json_object(text: str) -> str | None:
    """Return the first balanced JSON object in text, if one exists."""
    start = text.find("{")
    if start == -1:
        return None

    in_string = False
    escaped = False
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue

        if char == '"':
            in_string = True
        elif char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[start : index + 1]
    return None


def extract_loose_proof_value(text: str) -> str | None:
    """Extract a quoted proof value even if the model emits non-strict JSON."""
    match = re.search(r'"proof"\s*:\s*"', text)
    if match is None:
        return None

    chars: list[str] = []
    escaped = False
    for char in text[match.end() :]:
        if escaped:
            chars.append(
                {
                    "n": "\n",
                    "r": "\r",
                    "t": "\t",
                    '"': '"',
                    "\\": "\\",
                }.get(char, char)
            )
            escaped = False
        elif char == "\\":
            escaped = True
        elif char == '"':
            return "".join(chars)
        else:
            chars.append(char)
    return None


def replace_hole_marker(template: str, replacement_text: str) -> str:
    matches = list(HOLE_PATTERN.finditer(template))
    if len(matches) != 1:
        raise ProofError(
            f"Template must contain exactly one AI_PROOF_HOLE marker; found {len(matches)}."
        )

    match = matches[0]
    indent = match.group("indent")
    replacement = "\n".join(
        indent + line if line else "" for line in replacement_text.splitlines()
    )
    return template[: match.start()] + replacement + template[match.end() :]


def assemble(template: str, completion: str) -> str:
    return replace_hole_marker(template, normalize_completion(completion))


def minimize_simple_simp_completion(
    completion: str, diagnostics: str
) -> tuple[str, list[str]]:
    """Remove simple explicit simp arguments that Lean reports as unused."""
    match = SIMPLE_SIMP_PATTERN.fullmatch(completion.strip())
    if match is None:
        return completion, []

    unused = {
        warning.group("argument").strip()
        for warning in UNUSED_SIMP_ARGUMENT_PATTERN.finditer(diagnostics)
    }
    arguments = [
        argument.strip() for argument in match.group("arguments").split(",")
    ]
    removed = [argument for argument in arguments if argument in unused]
    if not removed:
        return completion, []

    retained = [argument for argument in arguments if argument not in unused]
    suffix = f" [{', '.join(retained)}]" if retained else ""
    return match.group("command") + suffix, removed


def remove_simple_simp_argument(completion: str, argument: str) -> str | None:
    """Return a simple simp completion with one explicit argument removed."""
    match = SIMPLE_SIMP_PATTERN.fullmatch(completion.strip())
    if match is None:
        return None
    arguments = [
        item.strip() for item in match.group("arguments").split(",")
    ]
    if argument not in arguments:
        return None
    retained = [item for item in arguments if item != argument]
    suffix = f" [{', '.join(retained)}]" if retained else ""
    return match.group("command") + suffix


def relative_to_root(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path.resolve())


def verify_lean(
    source: str, output_dir: Path, timeout: int, display_path: Path = DEFAULT_OUTPUT
) -> tuple[bool, str]:
    output_dir.mkdir(parents=True, exist_ok=True)
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".lean",
            prefix="AIProofCandidate_",
            dir=output_dir,
            delete=False,
        ) as candidate:
            candidate.write(source)
            temporary_path = Path(candidate.name)

        command_path = relative_to_root(temporary_path)
        try:
            result = subprocess.run(
                ["lake", "env", "lean", command_path],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout,
            )
        except FileNotFoundError as error:
            raise ProofError("Could not find `lake`; install Lean via elan first.") from error
        except subprocess.TimeoutExpired as error:
            return False, f"Lean verification timed out after {timeout} seconds: {error}"

        diagnostics = "\n".join(
            part.strip() for part in (result.stdout, result.stderr) if part.strip()
        )
        if temporary_path is not None:
            diagnostics = diagnostics.replace(str(temporary_path), relative_to_root(display_path))
            diagnostics = diagnostics.replace(command_path, relative_to_root(display_path))
        return result.returncode == 0, diagnostics
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


def build_prompt(
    template: str,
    contexts: Sequence[tuple[str, str]],
    forbidden_identifiers: Sequence[str] = (),
    instructions: Sequence[str] = (),
) -> str:
    context_text = "\n\n".join(
        f"--- {name} ---\n```lean\n{source}\n```" for name, source in contexts
    )
    forbidden_text = ""
    if forbidden_identifiers:
        forbidden_text = (
            "\nDo not use any of these unavailable identifiers:\n- "
            + "\n- ".join(forbidden_identifiers)
            + "\n"
        )
    instruction_text = ""
    if instructions:
        instruction_text = (
            "\nAdditional proof-search instructions:\n- "
            + "\n- ".join(instructions)
            + "\n"
        )
    return f"""Complete exactly the Lean 4 proof hole marked `-- AI_PROOF_HOLE`.

Return JSON with one string field named `proof`. The field must contain only the tactic
lines that replace the marker. Do not include `by`, Markdown fences, explanations,
declarations, `sorry`, `admit`, or `axiom`. Reuse the imported project lemmas where useful.
Prefer the shortest sufficient tactic. In particular, include only simp lemmas that are
necessary for this goal; do not append fallback tactics after a completed proof.
The result will be checked by Lean, so do not claim success without type-correct code.

Only modules imported by the target template are available during verification. The
project context below is reference source, not an additional import. If it contains a
theorem with the same conclusion as the target, copy and adapt that theorem's proof body;
do not invoke the theorem itself unless its module is imported by the target template.
When the reference explicitly says that its proof body has the same statement and
environment, preserve its tactic lines exactly; seemingly harmless additions such as
`at *` can change the induction hypothesis and break later rewrites.
{forbidden_text}{instruction_text}

Target template:
```lean
{template}
```

Available project context:
{context_text}
"""


def build_deepseek_prompt(
    task_template: str,
    contexts: Sequence[tuple[str, str]],
    forbidden_identifiers: Sequence[str] = (),
    instructions: Sequence[str] = (),
) -> str:
    task = replace_hole_marker(task_template, "sorry")
    context_text = "\n\n".join(
        f"--- {name} ---\n```lean4\n{source}\n```" for name, source in contexts
    )
    forbidden_text = ""
    if forbidden_identifiers:
        forbidden_text = (
            "\nThe completed proof must not use these unavailable identifiers:\n- "
            + "\n- ".join(forbidden_identifiers)
            + "\n"
        )
    instruction_text = ""
    if instructions:
        instruction_text = (
            "\nAdditional requirements:\n- " + "\n- ".join(instructions) + "\n"
        )
    return f"""You are completing a small Lean 4 theorem using the declarations below.
They are reference declarations only; do not reproduce them in the answer.

Relevant project declarations:
{context_text}
{forbidden_text}{instruction_text}
Complete the following Lean 4 code by replacing only `sorry` between
`{COMPLETION_BEGIN}` and `{COMPLETION_END}`:

```lean4
{task}
```

First give a brief proof plan of at most three sentences. Then provide the complete
corrected Lean 4 code in the final `lean4` code block. Preserve both completion marker
comments around the replacement. Do not leave `sorry`, `admit`, or `axiom` in the final
code. The code will be checked by Lean, so do not claim success without type-correct code.
"""


def build_transformers_prefill_prompt(
    task_template: str,
    contexts: Sequence[tuple[str, str]],
    forbidden_identifiers: Sequence[str] = (),
    instructions: Sequence[str] = (),
) -> tuple[str, str]:
    context_text = "\n\n".join(
        f"--- {name} ---\n```lean4\n{source}\n```" for name, source in contexts
    )
    forbidden_text = ""
    if forbidden_identifiers:
        forbidden_text = (
            "\nDo not use these unavailable identifiers:\n- "
            + "\n- ".join(forbidden_identifiers)
            + "\n"
        )
    instruction_text = ""
    if instructions:
        instruction_text = "\nAdditional requirements:\n- " + "\n- ".join(instructions) + "\n"

    matches = list(HOLE_PATTERN.finditer(task_template))
    if len(matches) != 1:
        raise ProofError(
            f"DeepSeek task must contain exactly one AI_PROOF_HOLE marker; found {len(matches)}."
        )
    match = matches[0]
    assistant_prefix = "```lean4\n" + task_template[: match.start()] + match.group("indent")
    task = replace_hole_marker(task_template, "sorry")
    prompt = f"""Complete the single `sorry` in this Lean 4 theorem.
Relevant declarations are provided first and are not part of the answer.

Relevant project declarations:
{context_text}
{forbidden_text}{instruction_text}
Target theorem:
```lean4
{task}
```

Your answer has already been started at the exact proof-hole indentation. Continue it
with the Lean tactic that replaces `sorry`. Put the tactic first; do not restart the
theorem and do not write a proof plan, Markdown, declarations, `sorry`, `admit`, or
`axiom`. Prefer the shortest sufficient tactic. In particular, include only simp lemmas
that are necessary for this goal. The completed original theorem will be checked by Lean.
"""
    return prompt, assistant_prefix


def extract_prefilled_completion(raw: str) -> str:
    """Use the first bracket-balanced tactic after a Transformers assistant prefill."""
    lines: list[str] = []
    balance = 0
    started = False
    for line in raw.splitlines():
        stripped = line.strip()
        if not started and (
            not stripped or stripped.startswith("```") or stripped.startswith("--")
        ):
            continue
        started = True
        lines.append(line)
        balance += sum(line.count(char) for char in "[({")
        balance -= sum(line.count(char) for char in "])}")
        if balance <= 0:
            return normalize_completion("\n".join(lines))
    return normalize_completion(raw)


def repair_prompt(base_prompt: str, failures: Sequence[dict[str, str]]) -> str:
    history_parts: list[str] = []
    for failure in failures[-2:]:
        completion = failure.get("completion", "")[-2000:]
        diagnostics = failure.get("diagnostics", "Lean exited unsuccessfully.")[-2500:]
        history_parts.append(
            f"""Attempt {failure.get('attempt', '?')} ({failure.get('status', 'failed')}):
Previous `proof` value:
```lean
{completion}
```
Diagnostics:
```text
{diagnostics}
```"""
        )
    history = "\n\n".join(history_parts)
    return f"""{base_prompt}

The following recent candidates failed. Do not repeat any of them:

{history}

Return a corrected JSON object using the same rules. Diagnose the actual type or tactic
error and switch proof strategy when a candidate is repeated.
"""


def repair_deepseek_prompt(
    base_prompt: str, failures: Sequence[dict[str, str]]
) -> str:
    history_parts: list[str] = []
    for failure in failures[-2:]:
        completion = failure.get("completion", "")[-1200:]
        diagnostics = failure.get("diagnostics", "Lean exited unsuccessfully.")[-2200:]
        history_parts.append(
            f"""Attempt {failure.get('attempt', '?')} ({failure.get('status', 'failed')}):
Extracted replacement:
```lean4
{completion}
```
Lean diagnostics:
```text
{diagnostics}
```"""
        )
    history = "\n\n".join(history_parts)
    return f"""{base_prompt}

The following recent replacements failed. Diagnose the Lean error and do not repeat them:

{history}

Return a revised brief plan followed by the complete corrected theorem in the final
`lean4` code block, preserving both completion marker comments.
"""


def repair_prefilled_prompt(
    base_prompt: str, failures: Sequence[dict[str, str]]
) -> str:
    history_parts: list[str] = []
    for failure in failures[-2:]:
        completion = failure.get("completion", "")[-500:]
        diagnostics = failure.get("diagnostics", "Lean exited unsuccessfully.")[-1800:]
        history_parts.append(
            f"""Rejected tactic from attempt {failure.get('attempt', '?')}:
```lean4
{completion}
```
Lean diagnostics:
```text
{diagnostics}
```"""
        )
    return f"""{base_prompt}

Previous first-line continuations failed:

{chr(10).join(history_parts)}

Continue the already-started assistant code with a different, corrected Lean tactic as
the very first generated line. Do not repeat a rejected tactic.
"""


def ollama_generate(
    ollama_url: str,
    model: str,
    prompt: str,
    temperature: float,
    timeout: int,
    use_json_schema: bool,
    think: str,
    num_predict: int,
    num_ctx: int,
    keep_alive: str,
) -> tuple[str, dict[str, Any]]:
    endpoint = ollama_url.rstrip("/") + "/api/generate"
    payload = {
        "model": model,
        "prompt": prompt,
        "stream": False,
        "keep_alive": keep_alive,
        "options": {
            "temperature": temperature,
            "num_predict": num_predict,
            "num_ctx": num_ctx,
        },
    }
    payload["think"] = (
        think.lower() == "true"
        if think.lower() in {"true", "false"}
        else think.lower()
    )
    if use_json_schema:
        payload["format"] = {
            "type": "object",
            "properties": {"proof": {"type": "string"}},
            "required": ["proof"],
            "additionalProperties": False,
        }
    request = urllib.request.Request(
        endpoint,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            response_payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as error:
        details = error.read().decode("utf-8", errors="replace")
        raise ProofError(f"Ollama HTTP {error.code}: {details}") from error
    except urllib.error.URLError as error:
        raise ProofError(
            f"Could not reach Ollama at {ollama_url}: {error.reason}. "
            "Start it with `ollama serve`."
        ) from error
    except (TimeoutError, json.JSONDecodeError) as error:
        raise ProofError(f"Invalid or timed-out response from Ollama: {error}") from error

    if "error" in response_payload:
        raise ProofError(f"Ollama error: {response_payload['error']}")
    generated = response_payload.get("response")
    if not isinstance(generated, str):
        raise ProofError("Ollama response did not contain a string `response` field.")
    metrics: dict[str, Any] = {}
    for key in (
        "created_at",
        "done",
        "done_reason",
        "total_duration",
        "load_duration",
        "prompt_eval_count",
        "prompt_eval_duration",
        "eval_count",
        "eval_duration",
    ):
        if key in response_payload:
            metrics[key] = response_payload[key]
    for key in ("total_duration", "load_duration", "prompt_eval_duration", "eval_duration"):
        value = metrics.get(key)
        if isinstance(value, int | float):
            metrics[key + "_seconds"] = round(value / 1_000_000_000, 6)
    thinking = response_payload.get("thinking")
    if isinstance(thinking, str):
        metrics["thinking_characters"] = len(thinking)
    return generated, metrics


def ollama_chat(
    ollama_url: str,
    model: str,
    prompt: str,
    temperature: float,
    timeout: int,
    num_predict: int,
    num_ctx: int,
    keep_alive: str,
) -> tuple[str, dict[str, Any]]:
    """Call Ollama's chat endpoint using the model's native chat template."""
    endpoint = ollama_url.rstrip("/") + "/api/chat"
    payload = {
        "model": model,
        "messages": [{"role": "user", "content": prompt}],
        "stream": False,
        "keep_alive": keep_alive,
        "options": {
            "temperature": temperature,
            "num_predict": num_predict,
            "num_ctx": num_ctx,
        },
    }
    request = urllib.request.Request(
        endpoint,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            response_payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as error:
        details = error.read().decode("utf-8", errors="replace")
        raise ProofError(f"Ollama HTTP {error.code}: {details}") from error
    except urllib.error.URLError as error:
        raise ProofError(
            f"Could not reach Ollama at {ollama_url}: {error.reason}. "
            "Start it with `ollama serve`."
        ) from error
    except (TimeoutError, json.JSONDecodeError) as error:
        raise ProofError(f"Invalid or timed-out response from Ollama: {error}") from error

    if "error" in response_payload:
        raise ProofError(f"Ollama error: {response_payload['error']}")
    message = response_payload.get("message")
    generated = message.get("content") if isinstance(message, dict) else None
    if not isinstance(generated, str):
        raise ProofError("Ollama chat response did not contain `message.content`.")
    metrics: dict[str, Any] = {}
    for key in (
        "created_at",
        "done",
        "done_reason",
        "total_duration",
        "load_duration",
        "prompt_eval_count",
        "prompt_eval_duration",
        "eval_count",
        "eval_duration",
    ):
        if key in response_payload:
            metrics[key] = response_payload[key]
    for key in ("total_duration", "load_duration", "prompt_eval_duration", "eval_duration"):
        value = metrics.get(key)
        if isinstance(value, int | float):
            metrics[key + "_seconds"] = round(value / 1_000_000_000, 6)
    return generated, metrics


class TransformersRunner:
    """Lazily loaded official Hugging Face inference backend."""

    def __init__(
        self,
        model_id: str,
        cache_dir: Path,
        device_name: str,
        gpu_memory_gib: float,
    ) -> None:
        os.environ.setdefault("TOKENIZERS_PARALLELISM", "false")
        try:
            import torch
            from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer
        except ImportError as error:
            raise ProofError(
                "Transformers backend dependencies are missing. Run the documented "
                "`.venv-deepseek` installation command first."
            ) from error

        requested_device = device_name
        self.requested_device = requested_device
        if device_name == "auto":
            if torch.cuda.is_available():
                device_name = "cuda"
            elif torch.backends.mps.is_available():
                device_name = "mps"
            else:
                device_name = "cpu"
        if device_name == "cuda" and not torch.cuda.is_available():
            raise ProofError(
                "CUDA was requested, but PyTorch cannot access a CUDA device. "
                "Install a CUDA-enabled PyTorch build and check the NVIDIA driver, "
                "or use --device cpu."
            )
        if device_name == "mps" and not torch.backends.mps.is_available():
            raise ProofError(
                "MPS was requested, but this PyTorch build or Mac does not support it. "
                "Use --device cpu instead."
            )
        self.torch = torch
        self.device = torch.device(device_name)
        self.gpu_memory_gib = gpu_memory_gib
        model_max_memory: dict[int | str, int] | None = None
        device_map: str | None = None
        config = AutoConfig.from_pretrained(
            model_id,
            cache_dir=cache_dir,
            trust_remote_code=True,
        )
        rope_scaling = getattr(config, "rope_scaling", None)
        if isinstance(rope_scaling, dict):
            for key in ("factor", "beta_fast", "beta_slow"):
                if isinstance(rope_scaling.get(key), int):
                    rope_scaling[key] = float(rope_scaling[key])

        if self.device.type == "cuda":
            total_gpu_bytes = torch.cuda.get_device_properties(0).total_memory
            requested_gpu_bytes = int(gpu_memory_gib * 2**30)
            if requested_gpu_bytes <= 0:
                raise ProofError("--gpu-memory-gib must be greater than zero.")
            if requested_gpu_bytes > total_gpu_bytes:
                raise ProofError(
                    f"--gpu-memory-gib ({gpu_memory_gib:g}) exceeds available GPU "
                    f"memory ({total_gpu_bytes / 2**30:.2f} GiB)."
                )
            # Leave one GiB inside the requested ceiling for the CUDA context,
            # KV cache, activations, and temporary generation tensors.
            model_gpu_bytes = max(requested_gpu_bytes - 2**30, 1 * 2**30)
            allocator_gpu_bytes = max(requested_gpu_bytes - 512 * 2**20, 1 * 2**30)
            torch.cuda.set_per_process_memory_fraction(
                min(allocator_gpu_bytes / total_gpu_bytes, 1.0), 0
            )
            model_max_memory = {0: model_gpu_bytes, "cpu": 64 * 2**30}
            device_map = "auto"
            model_dtype = (
                torch.bfloat16
                if torch.cuda.is_bf16_supported()
                else torch.float16
            )
        elif self.device.type == "mps":
            model_dtype = torch.float16
        else:
            configured_dtype = getattr(config, "torch_dtype", None)
            model_dtype = (
                configured_dtype
                if configured_dtype in {torch.bfloat16, torch.float32}
                else torch.float32
            )
        self.model_dtype = model_dtype
        load_started = time.perf_counter()
        print(
            f"Transformers device: requested={requested_device}, "
            f"resolved={self.device}, dtype={model_dtype}, "
            f"gpu_memory_limit={gpu_memory_gib:g} GiB",
            flush=True,
        )
        print(
            f"Loading official Transformers model {model_id} on {self.device} "
            f"({model_dtype})...",
            flush=True,
        )
        self.tokenizer = AutoTokenizer.from_pretrained(
            model_id,
            cache_dir=cache_dir,
            trust_remote_code=True,
        )
        self.model = AutoModelForCausalLM.from_pretrained(
            model_id,
            cache_dir=cache_dir,
            config=config,
            torch_dtype=model_dtype,
            low_cpu_mem_usage=True,
            trust_remote_code=True,
            device_map=device_map,
            max_memory=model_max_memory,
        )
        if device_map is None:
            self.model.to(self.device)
        self.model.eval()
        self.load_seconds = elapsed_seconds(load_started)
        print(f"Transformers model loaded in {self.load_seconds:.3f}s.", flush=True)

    def generate(
        self,
        prompt: str,
        num_predict: int,
        timeout: int,
        assistant_prefix: str | None = None,
    ) -> tuple[str, dict[str, Any]]:
        started = time.perf_counter()
        chat = [{"role": "user", "content": prompt}]
        if assistant_prefix is not None:
            chat.append({"role": "assistant", "content": assistant_prefix})
        encoded = self.tokenizer.apply_chat_template(
            chat,
            tokenize=True,
            add_generation_prompt=assistant_prefix is None,
            continue_final_message=assistant_prefix is not None,
            return_dict=True,
            return_tensors="pt",
        )
        encoded = encoded.to(self.device)
        inputs = encoded["input_ids"]
        try:
            with self.torch.inference_mode():
                outputs = self.model.generate(
                    inputs,
                    attention_mask=encoded.get("attention_mask"),
                    max_new_tokens=num_predict,
                    max_time=float(timeout),
                    do_sample=False,
                    pad_token_id=self.tokenizer.eos_token_id,
                )
        except RuntimeError as error:
            message = str(error)
            if "out of memory" in message.lower():
                raise ProofError(
                    f"Transformers ran out of memory on {self.device}. Reduce the "
                    "model size or token limits, or use a quantized Ollama model."
                ) from error
            raise ProofError(f"Transformers generation failed: {message}") from error
        generated_tokens = outputs[0, inputs.shape[-1] :]
        generated = self.tokenizer.decode(generated_tokens, skip_special_tokens=True)
        return generated, {
            "backend": "transformers",
            "device": str(self.device),
            "requested_device": self.requested_device,
            "dtype": str(self.model_dtype),
            "gpu_memory_limit_gib": self.gpu_memory_gib,
            "load_seconds": self.load_seconds,
            "prompt_eval_count": int(inputs.shape[-1]),
            "eval_count": int(generated_tokens.shape[-1]),
            "generation_timeout_seconds": timeout,
            "total_duration_seconds": elapsed_seconds(started),
        }


def write_verified_result(
    completion: str, source: str, completion_path: Path, output_path: Path
) -> None:
    completion_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    completion_path.write_text(completion.rstrip() + "\n", encoding="utf-8")
    output_path.write_text(source, encoding="utf-8")


def resolve_config_path(value: str | Path) -> Path:
    """Resolve a configuration path relative to the repository root."""
    path = Path(value).expanduser()
    return path.resolve() if path.is_absolute() else (ROOT / path).resolve()


def load_config(path: Path) -> dict[str, Any]:
    """Load and type-check JSON defaults for the command-line parser."""
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except OSError as error:
        raise ProofError(f"Could not read configuration file {path}: {error}") from error
    except json.JSONDecodeError as error:
        raise ProofError(
            f"Invalid JSON in configuration file {path} at "
            f"line {error.lineno}, column {error.colno}: {error.msg}"
        ) from error

    if not isinstance(raw, dict):
        raise ProofError("Configuration must be a JSON object.")

    unknown = sorted(set(raw) - CONFIG_ALLOWED_KEYS)
    if unknown:
        raise ProofError("Unknown configuration field(s): " + ", ".join(unknown))

    schema_version = raw.get("schema_version", 1)
    if schema_version != 1:
        raise ProofError(
            f"Unsupported configuration schema_version {schema_version!r}; expected 1."
        )

    config = {key: value for key, value in raw.items() if key != "schema_version"}

    for key in CONFIG_PATH_KEYS & config.keys():
        value = config[key]
        if not isinstance(value, str) or not value:
            raise ProofError(f"Configuration field `{key}` must be a non-empty path string.")
        config[key] = resolve_config_path(value)

    for key in CONFIG_PATH_LIST_KEYS & config.keys():
        value = config[key]
        if not isinstance(value, list) or not all(
            isinstance(item, str) and item for item in value
        ):
            raise ProofError(
                f"Configuration field `{key}` must be a list of non-empty path strings."
            )
        config[key] = [resolve_config_path(item) for item in value]

    for key in CONFIG_STRING_LIST_KEYS & config.keys():
        value = config[key]
        if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
            raise ProofError(f"Configuration field `{key}` must be a list of strings.")

    for key in CONFIG_STRING_KEYS & config.keys():
        if not isinstance(config[key], str) or not config[key]:
            raise ProofError(f"Configuration field `{key}` must be a non-empty string.")

    for key in CONFIG_INTEGER_KEYS & config.keys():
        if isinstance(config[key], bool) or not isinstance(config[key], int):
            raise ProofError(f"Configuration field `{key}` must be an integer.")

    for key in CONFIG_NUMBER_KEYS & config.keys():
        if isinstance(config[key], bool) or not isinstance(config[key], int | float):
            raise ProofError(f"Configuration field `{key}` must be a number.")

    for key in CONFIG_BOOLEAN_KEYS & config.keys():
        if not isinstance(config[key], bool):
            raise ProofError(f"Configuration field `{key}` must be true or false.")

    return config


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    raw_argv = list(argv) if argv is not None else sys.argv[1:]
    config_parser = argparse.ArgumentParser(add_help=False)
    config_parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    config_args, _ = config_parser.parse_known_args(raw_argv)
    config_path = resolve_config_path(config_args.config)
    try:
        config_defaults = load_config(config_path)
    except ProofError as error:
        config_parser.error(str(error))

    parser = argparse.ArgumentParser(
        description="Generate a proof with a local model and verify every candidate with Lean."
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=config_path,
        help=(
            "JSON configuration file. Relative paths inside it are resolved from the "
            "repository root (default: AI_Proof_Demo/config.json)."
        ),
    )
    parser.add_argument(
        "--backend",
        choices=("ollama", "transformers"),
        default=os.environ.get("AI_PROOF_BACKEND", "transformers"),
    )
    parser.add_argument(
        "--device",
        choices=("auto", "cpu", "cuda", "mps"),
        default=os.environ.get("AI_PROOF_DEVICE", "auto"),
        help=(
            "Transformers device: cpu, cuda, mps, or auto-detect an accelerator "
            "(default: auto)."
        ),
    )
    parser.add_argument(
        "--gpu-memory-gib",
        type=float,
        default=DEFAULT_GPU_MEMORY_GIB,
        help=(
            "Maximum CUDA memory budget in GiB. Model weights above the reserved "
            "GPU budget are offloaded to CPU (default: 8)."
        ),
    )
    parser.add_argument(
        "--model",
        default=os.environ.get("AI_PROOF_MODEL"),
    )
    parser.add_argument(
        "--ollama-url", default=os.environ.get("OLLAMA_URL", DEFAULT_OLLAMA_URL)
    )
    parser.add_argument(
        "--prompt-mode",
        choices=("auto", "tactics", "deepseek-prover"),
        default="auto",
        help="Prompt and response protocol; auto selects DeepSeek-Prover by model name.",
    )
    parser.add_argument("--template", type=Path, default=DEFAULT_TEMPLATE)
    parser.add_argument(
        "--deepseek-task",
        type=Path,
        default=DEFAULT_DEEPSEEK_TASK,
        help="Standalone local-goal template used by the DeepSeek-Prover prompt mode.",
    )
    parser.add_argument("--completion", type=Path, default=DEFAULT_COMPLETION)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--context",
        action="append",
        type=Path,
        help="Lean source to include in the prompt; repeat for multiple files.",
    )
    parser.add_argument(
        "--forbid-identifier",
        action="append",
        default=[],
        help="Reject a candidate containing this unavailable identifier; repeatable.",
    )
    parser.add_argument(
        "--instruction",
        action="append",
        default=[],
        help="Additional proof-search instruction to include in the prompt; repeatable.",
    )
    parser.add_argument("--attempts", type=int, default=3)
    parser.add_argument("--temperature", type=float, default=0.0)
    parser.add_argument(
        "--think",
        choices=("false", "true", "low", "medium", "high"),
        default=os.environ.get("OLLAMA_THINK", DEFAULT_THINK),
        help="Ollama thinking mode or reasoning effort for tactics mode (default: false).",
    )
    parser.add_argument(
        "--num-predict",
        type=int,
        default=512,
        help="Maximum tokens generated for each proof candidate.",
    )
    parser.add_argument(
        "--prefill-num-predict",
        type=int,
        default=96,
        help="Token cap for code-first Transformers continuation (default: 96).",
    )
    parser.add_argument(
        "--num-ctx",
        type=int,
        default=4096,
        help="Ollama context-window size for prompt, reasoning, and response tokens.",
    )
    parser.add_argument(
        "--generation-timeout",
        type=int,
        default=600,
        help=(
            "Maximum generation time in seconds for either backend. Transformers "
            "may finish its current decoding step slightly after the limit."
        ),
    )
    parser.add_argument(
        "--keep-alive",
        default="30m",
        help="How long Ollama keeps the model loaded between repair attempts.",
    )
    parser.add_argument(
        "--transformers-cache",
        type=Path,
        default=ROOT / ".cache" / "huggingface",
        help="Workspace-local cache for official Hugging Face model files.",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="Use only locally cached Hugging Face files; disable Hub network access.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Seconds to wait for each Lean verification.",
    )
    parser.add_argument(
        "--json-schema",
        action="store_true",
        help=(
            "Ask Ollama to enforce a JSON schema. Disabled by default because "
            "some local models produce worse or empty responses in this mode."
        ),
    )
    parser.add_argument(
        "--verify-only",
        action="store_true",
        help="Skip model generation and verify the current completion file.",
    )
    parser.add_argument(
        "--log-dir",
        type=Path,
        default=Path(os.environ.get("AI_PROOF_LOG_DIR", DEFAULT_LOG_DIR)),
        help="Directory for persistent per-run JSON records.",
    )
    parser.add_argument(
        "--no-log",
        action="store_true",
        help="Disable persistent JSON run logging.",
    )
    parser.set_defaults(**config_defaults)
    args = parser.parse_args(raw_argv)
    args.config = config_path
    if args.backend not in {"ollama", "transformers"}:
        parser.error("--backend must be `ollama` or `transformers`")
    if args.prompt_mode not in {"auto", "tactics", "deepseek-prover"}:
        parser.error(
            "--prompt-mode must be `auto`, `tactics`, or `deepseek-prover`"
        )
    if args.think not in {"false", "true", "low", "medium", "high"}:
        parser.error("--think must be false, true, low, medium, or high")
    if not args.model:
        args.model = (
            DEFAULT_TRANSFORMERS_MODEL
            if args.backend == "transformers"
            else os.environ.get("OLLAMA_MODEL") or DEFAULT_MODEL
        )
    if args.attempts < 1:
        parser.error("--attempts must be at least 1")
    if args.gpu_memory_gib <= 0:
        parser.error("--gpu-memory-gib must be greater than zero")
    if args.timeout < 1:
        parser.error("--timeout must be at least 1")
    if args.generation_timeout < 1:
        parser.error("--generation-timeout must be at least 1")
    if args.num_predict < 1:
        parser.error("--num-predict must be at least 1")
    if args.prefill_num_predict < 1:
        parser.error("--prefill-num-predict must be at least 1")
    if args.num_ctx < 1:
        parser.error("--num-ctx must be at least 1")
    if not args.keep_alive:
        parser.error("--keep-alive must not be empty")
    if not 0 <= args.temperature <= 2:
        parser.error("--temperature must be between 0 and 2")
    return args


def resolve_prompt_mode(model: str, requested_mode: str) -> str:
    if requested_mode != "auto":
        return requested_mode
    return (
        "deepseek-prover"
        if DEEPSEEK_MODEL_FRAGMENT in model.lower()
        else "tactics"
    )


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.offline:
        os.environ["HF_HUB_OFFLINE"] = "1"
        os.environ["TRANSFORMERS_OFFLINE"] = "1"
    argv_for_log = list(argv) if argv is not None else sys.argv[1:]
    logger = RunLogger(args, argv_for_log, not args.no_log)

    def handle_termination(_signum: int, _frame: Any) -> None:
        raise KeyboardInterrupt

    for signal_name in ("SIGHUP", "SIGTERM"):
        termination_signal = getattr(signal, signal_name, None)
        if termination_signal is not None:
            signal.signal(termination_signal, handle_termination)
    try:
        template = read_text(args.template, "template")
        output_path = args.output.resolve()
        completion_path = args.completion.resolve()
        logger.record["inputs"]["template"] = {
            "path": relative_to_root(args.template),
            "sha256": sha256_text(template),
            "characters": len(template),
        }

        if args.verify_only:
            completion = normalize_completion(
                read_text(completion_path, "completion")
            )
            logger.record["inputs"]["completion"] = {
                "path": relative_to_root(completion_path),
                "sha256": sha256_text(completion),
                "characters": len(completion),
            }
            generated = assemble(template, completion)
            verification_started = time.perf_counter()
            passed, diagnostics = verify_lean(
                generated, output_path.parent, args.timeout, output_path
            )
            logger.record["verification"] = {
                "passed": passed,
                "duration_seconds": elapsed_seconds(verification_started),
                "diagnostics": diagnostics,
            }
            if not passed:
                if diagnostics:
                    print(diagnostics, file=sys.stderr)
                print("Lean verification failed.", file=sys.stderr)
                logger.finish("verification_failed", 1)
                return 1
            write_verified_result(completion, generated, completion_path, output_path)
            print("Lean verification passed.")
            print(f"Generated file: {relative_to_root(output_path)}")
            logger.finish("verification_passed", 0)
            return 0

        context_paths = args.context or [DEFAULT_CONTEXT]
        contexts = [
            (relative_to_root(path), read_text(path, "context file"))
            for path in context_paths
        ]
        logger.record["configuration"]["contexts"] = [
            relative_to_root(path) for path in context_paths
        ]
        logger.record["inputs"]["contexts"] = [
            {
                "path": name,
                "sha256": sha256_text(source),
                "characters": len(source),
            }
            for name, source in contexts
        ]
        prompt_mode = resolve_prompt_mode(args.model, args.prompt_mode)
        logger.record["configuration"]["resolved_prompt_mode"] = prompt_mode
        assistant_prefix: str | None = None
        if prompt_mode == "deepseek-prover":
            if args.json_schema:
                raise ProofError(
                    "DeepSeek-Prover prompt mode does not use --json-schema; "
                    "remove that option."
                )
            deepseek_task = read_text(args.deepseek_task, "DeepSeek local-goal template")
            logger.record["inputs"]["deepseek_task"] = {
                "path": relative_to_root(args.deepseek_task),
                "sha256": sha256_text(deepseek_task),
                "characters": len(deepseek_task),
            }
            if args.backend == "transformers":
                base_prompt, assistant_prefix = build_transformers_prefill_prompt(
                    deepseek_task,
                    contexts,
                    args.forbid_identifier,
                    args.instruction,
                )
                normalize_model_output = extract_prefilled_completion
                repair_model_prompt = repair_prefilled_prompt
            else:
                base_prompt = build_deepseek_prompt(
                    deepseek_task,
                    contexts,
                    args.forbid_identifier,
                    args.instruction,
                )
                normalize_model_output = extract_deepseek_completion
                repair_model_prompt = repair_deepseek_prompt
        else:
            base_prompt = build_prompt(
                template, contexts, args.forbid_identifier, args.instruction
            )
            normalize_model_output = normalize_completion
            repair_model_prompt = repair_prompt
        logger.record["prompt"] = {
            "base_sha256": sha256_text(base_prompt),
            "base_characters": len(base_prompt),
        }
        logger.save()
        prompt = base_prompt
        failures: list[dict[str, str]] = []
        seen_completions: dict[str, int] = {}
        transformers_runner: TransformersRunner | None = None

        for attempt in range(1, args.attempts + 1):
            attempt_started = time.perf_counter()
            attempt_record: dict[str, Any] = {
                "attempt": attempt,
                "started_at": utc_now(),
                "finished_at": None,
                "duration_seconds": None,
                "status": "running",
                "prompt_sha256": sha256_text(prompt),
                "prompt_characters": len(prompt),
                "generation_seconds": 0.0,
                "verification_seconds": 0.0,
            }
            logger.start_attempt(attempt_record)
            print(f"Attempt {attempt}/{args.attempts}: asking {args.model}...", flush=True)
            generation_started = time.perf_counter()
            try:
                if args.backend == "transformers":
                    if transformers_runner is None:
                        transformers_runner = TransformersRunner(
                            args.model,
                            args.transformers_cache,
                            args.device,
                            args.gpu_memory_gib,
                        )
                        logger.record["configuration"]["resolved_device"] = str(
                            transformers_runner.device
                        )
                        logger.record["configuration"]["model_dtype"] = str(
                            transformers_runner.model_dtype
                        )
                        logger.save()
                    raw, generation_metrics = transformers_runner.generate(
                        prompt,
                        args.prefill_num_predict
                        if assistant_prefix is not None
                        else args.num_predict,
                        args.generation_timeout,
                        assistant_prefix,
                    )
                elif prompt_mode == "deepseek-prover":
                    raw, generation_metrics = ollama_chat(
                        args.ollama_url,
                        args.model,
                        prompt,
                        args.temperature,
                        args.generation_timeout,
                        args.num_predict,
                        args.num_ctx,
                        args.keep_alive,
                    )
                else:
                    raw, generation_metrics = ollama_generate(
                        args.ollama_url,
                        args.model,
                        prompt,
                        args.temperature,
                        args.generation_timeout,
                        args.json_schema,
                        args.think,
                        args.num_predict,
                        args.num_ctx,
                        args.keep_alive,
                    )
            except ProofError as error:
                attempt_record["generation_seconds"] = elapsed_seconds(generation_started)
                attempt_record["status"] = "model_error"
                attempt_record["error"] = str(error)
                logger.finish_attempt(attempt_record, attempt_started)
                raise
            except KeyboardInterrupt:
                attempt_record["generation_seconds"] = elapsed_seconds(generation_started)
                attempt_record["status"] = "interrupted"
                attempt_record["error"] = "Interrupted by user"
                logger.finish_attempt(attempt_record, attempt_started)
                raise
            attempt_record["generation_seconds"] = elapsed_seconds(generation_started)
            attempt_record["generation_metrics"] = generation_metrics
            attempt_record["raw_response"] = raw
            try:
                completion = normalize_model_output(raw)
                for identifier in args.forbid_identifier:
                    if identifier in completion:
                        raise ProofError(
                            f"Completion uses forbidden unavailable identifier: {identifier}"
                        )
                generated = assemble(template, completion)
            except ProofError as error:
                diagnostics = str(error)
                attempt_record["status"] = "rejected_before_lean"
                attempt_record["diagnostics"] = diagnostics
                print(f"Candidate rejected before Lean: {diagnostics}", file=sys.stderr)
                failures.append(
                    {
                        "attempt": str(attempt),
                        "status": "rejected_before_lean",
                        "completion": raw,
                        "diagnostics": diagnostics,
                    }
                )
                prompt = repair_model_prompt(base_prompt, failures)
                logger.finish_attempt(attempt_record, attempt_started)
                continue

            attempt_record["completion"] = completion
            previous_attempt = seen_completions.get(completion)
            seen_completions[completion] = attempt
            if previous_attempt is not None:
                attempt_record["duplicate_of_attempt"] = previous_attempt
            verification_started = time.perf_counter()
            passed, diagnostics = verify_lean(
                generated, output_path.parent, args.timeout, output_path
            )
            if passed:
                minimization_steps: list[dict[str, Any]] = []
                while True:
                    minimized_completion, removed_arguments = (
                        minimize_simple_simp_completion(completion, diagnostics)
                    )
                    if not removed_arguments:
                        break
                    minimized_generated = assemble(template, minimized_completion)
                    minimized_passed, minimized_diagnostics = verify_lean(
                        minimized_generated,
                        output_path.parent,
                        args.timeout,
                        output_path,
                    )
                    minimization_steps.append(
                        {
                            "from": completion,
                            "removed_arguments": removed_arguments,
                            "to": minimized_completion,
                            "passed": minimized_passed,
                            "diagnostics": minimized_diagnostics,
                        }
                    )
                    if not minimized_passed:
                        break
                    completion = minimized_completion
                    generated = minimized_generated
                    diagnostics = minimized_diagnostics
                    attempt_record["completion"] = completion
                # The linter only reports arguments that were unused in the current
                # combination. Greedily test the remaining arguments as well, since a
                # proof can still work after removing an argument that the linter used.
                while True:
                    simple_match = SIMPLE_SIMP_PATTERN.fullmatch(completion.strip())
                    if simple_match is None:
                        break
                    remaining_arguments = [
                        item.strip()
                        for item in simple_match.group("arguments").split(",")
                    ]
                    accepted_removal = False
                    # Prefer removing trailing arguments first. Generated simp calls
                    # usually put the goal-specific lemmas first and generic fallback
                    # rewrites at the end.
                    for argument in reversed(remaining_arguments):
                        trial_completion = remove_simple_simp_argument(
                            completion, argument
                        )
                        if trial_completion is None:
                            continue
                        trial_generated = assemble(template, trial_completion)
                        trial_passed, trial_diagnostics = verify_lean(
                            trial_generated,
                            output_path.parent,
                            args.timeout,
                            output_path,
                        )
                        minimization_steps.append(
                            {
                                "from": completion,
                                "removed_arguments": [argument],
                                "to": trial_completion,
                                "passed": trial_passed,
                                "diagnostics": trial_diagnostics,
                            }
                        )
                        if trial_passed:
                            completion = trial_completion
                            generated = trial_generated
                            diagnostics = trial_diagnostics
                            attempt_record["completion"] = completion
                            accepted_removal = True
                            break
                    if not accepted_removal:
                        break
                if minimization_steps:
                    attempt_record["simp_minimization"] = {
                        "steps": minimization_steps,
                        "final_completion": completion,
                    }
            attempt_record["verification_seconds"] = elapsed_seconds(verification_started)
            attempt_record["diagnostics"] = diagnostics
            if passed:
                attempt_record["status"] = "success"
                write_verified_result(completion, generated, completion_path, output_path)
                logger.finish_attempt(attempt_record, attempt_started)
                print("Lean verification passed.")
                print(f"Completion: {relative_to_root(completion_path)}")
                print(f"Generated file: {relative_to_root(output_path)}")
                logger.finish("success", 0)
                return 0

            attempt_record["status"] = "lean_failed"
            print("Lean verification failed for this candidate.", file=sys.stderr)
            print("Candidate proof:", file=sys.stderr)
            print(completion, file=sys.stderr)
            if diagnostics:
                print(diagnostics, file=sys.stderr)
            duplicate_note = (
                f"\nThis proof exactly duplicates attempt {previous_attempt}; switch strategy."
                if previous_attempt is not None
                else ""
            )
            failures.append(
                {
                    "attempt": str(attempt),
                    "status": "lean_failed",
                    "completion": completion,
                    "diagnostics": diagnostics + duplicate_note,
                }
            )
            prompt = repair_model_prompt(base_prompt, failures)
            logger.finish_attempt(attempt_record, attempt_started)

        print(
            f"No candidate passed Lean after {args.attempts} attempts; "
            "verified output files were left unchanged.",
            file=sys.stderr,
        )
        logger.finish("attempts_exhausted", 1)
        return 1
    except ProofError as error:
        print(f"error: {error}", file=sys.stderr)
        logger.finish("error", 2, str(error))
        return 2
    except KeyboardInterrupt:
        print("Interrupted by user.", file=sys.stderr)
        logger.finish("interrupted", 130, "Interrupted by user")
        return 130
    except Exception as error:
        logger.finish("unexpected_error", 3, repr(error))
        raise


if __name__ == "__main__":
    raise SystemExit(main())
