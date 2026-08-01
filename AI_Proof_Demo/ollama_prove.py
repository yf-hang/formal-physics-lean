#!/usr/bin/env python3
"""Generate a Lean proof with Ollama and accept it only after Lean verifies it."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
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
DEFAULT_OUTPUT = ROOT / "CosmoLattice" / "AIProofGenerated.lean"
DEFAULT_CONTEXT = ROOT / "AI_Proof_Demo" / "FiniteDiffProofReference.txt"
DEFAULT_OLLAMA_URL = "http://127.0.0.1:11434"
DEFAULT_MODEL = "gpt-oss:20b"
DEFAULT_THINK = "low"
DEFAULT_LOG_DIR = ROOT / "AI_Proof_Demo" / "runs"
HOLE_PATTERN = re.compile(
    r"^(?P<indent>[ \t]*)-- AI_PROOF_HOLE[ \t]*$", re.MULTILINE
)
FORBIDDEN_PATTERN = re.compile(r"\b(?:sorry|admit|axiom)\b", re.IGNORECASE)
TOP_LEVEL_COMMAND_PATTERN = re.compile(
    r"^[ \t]*(?:import|namespace|section|end|theorem|lemma|def|example|"
    r"instance|class|structure|inductive)\b",
    re.IGNORECASE | re.MULTILINE,
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
                "mode": "verify_only" if args.verify_only else "generate",
                "model": args.model,
                "ollama_url": args.ollama_url,
                "template": relative_to_root(args.template),
                "completion": relative_to_root(args.completion),
                "output": relative_to_root(args.output),
                "contexts": [relative_to_root(path) for path in (args.context or [])],
                "attempts": args.attempts,
                "temperature": args.temperature,
                "think": args.think,
                "num_predict": args.num_predict,
                "num_ctx": args.num_ctx,
                "generation_timeout_seconds": args.generation_timeout,
                "lean_timeout_seconds": args.timeout,
                "json_schema": args.json_schema,
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


def assemble(template: str, completion: str) -> str:
    matches = list(HOLE_PATTERN.finditer(template))
    if len(matches) != 1:
        raise ProofError(
            f"Template must contain exactly one AI_PROOF_HOLE marker; found {len(matches)}."
        )

    completion = normalize_completion(completion)
    match = matches[0]
    indent = match.group("indent")
    replacement = "\n".join(
        indent + line if line else "" for line in completion.splitlines()
    )
    return template[: match.start()] + replacement + template[match.end() :]


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
) -> tuple[str, dict[str, Any]]:
    endpoint = ollama_url.rstrip("/") + "/api/generate"
    payload = {
        "model": model,
        "prompt": prompt,
        "stream": False,
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


def write_verified_result(
    completion: str, source: str, completion_path: Path, output_path: Path
) -> None:
    completion_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    completion_path.write_text(completion.rstrip() + "\n", encoding="utf-8")
    output_path.write_text(source, encoding="utf-8")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate a proof with local Ollama and verify every candidate with Lean."
    )
    parser.add_argument(
        "--model", default=os.environ.get("OLLAMA_MODEL", DEFAULT_MODEL)
    )
    parser.add_argument(
        "--ollama-url", default=os.environ.get("OLLAMA_URL", DEFAULT_OLLAMA_URL)
    )
    parser.add_argument("--template", type=Path, default=DEFAULT_TEMPLATE)
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
        help="Ollama thinking mode or reasoning effort (default: low).",
    )
    parser.add_argument(
        "--num-predict",
        type=int,
        default=1400,
        help="Maximum tokens generated for each proof candidate.",
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
        help="Seconds to wait for each local-model response.",
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
            "gpt-oss:20b can return an empty response in this mode."
        ),
    )
    parser.add_argument(
        "--verify-only",
        action="store_true",
        help="Skip Ollama and verify the current completion file.",
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
    args = parser.parse_args(argv)
    if args.attempts < 1:
        parser.error("--attempts must be at least 1")
    if args.timeout < 1:
        parser.error("--timeout must be at least 1")
    if args.generation_timeout < 1:
        parser.error("--generation-timeout must be at least 1")
    if args.num_predict < 1:
        parser.error("--num-predict must be at least 1")
    if args.num_ctx < 1:
        parser.error("--num-ctx must be at least 1")
    if not 0 <= args.temperature <= 2:
        parser.error("--temperature must be between 0 and 2")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    argv_for_log = list(argv) if argv is not None else sys.argv[1:]
    logger = RunLogger(args, argv_for_log, not args.no_log)
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
        base_prompt = build_prompt(
            template, contexts, args.forbid_identifier, args.instruction
        )
        logger.record["prompt"] = {
            "base_sha256": sha256_text(base_prompt),
            "base_characters": len(base_prompt),
        }
        logger.save()
        prompt = base_prompt
        failures: list[dict[str, str]] = []
        seen_completions: dict[str, int] = {}

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
                raw, ollama_metrics = ollama_generate(
                    args.ollama_url,
                    args.model,
                    prompt,
                    args.temperature,
                    args.generation_timeout,
                    args.json_schema,
                    args.think,
                    args.num_predict,
                    args.num_ctx,
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
            attempt_record["ollama_metrics"] = ollama_metrics
            attempt_record["raw_response"] = raw
            try:
                completion = normalize_completion(raw)
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
                prompt = repair_prompt(base_prompt, failures)
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
            prompt = repair_prompt(base_prompt, failures)
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
