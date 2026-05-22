## TwoSiteBooleanLattice

This Lean project formalizes the Boolean expansion for the two-site $\ell$-loop cosmological wavefunction coefficients.

The expansion formula is
```math
\prod_{i=1}^{\ell+1}\Delta_{y_i}\left[\frac{1}{D}\right]
=\left(\prod_{i=1}^{\ell+1} y_i\right)
\sum_{\pi\in\mathfrak{S}_{\ell+1}}
\frac{1}{
D_{\varnothing}\,
D_{\{Y_{\pi_1}\}}\,
D_{\{Y_{\pi_1},Y_{\pi_2}\}}\cdots
D_{\boldsymbol{Y}}}
```

For $\ell = 1$, $\boldsymbol{Y}=\{Y_1,Y_2\}$:
```math
\begin{aligned}
\prod_{i=1}^{2}\Delta_{y_i}\left[\frac{1}{D}\right]
&=\frac1{D_\varnothing}
-\frac1{D_{\{Y_1\}}}
-\frac1{D_{\{Y_2\}}}
+\frac1{D_{\boldsymbol{Y}}}
\\
&= y_1y_2\left(\frac1{D_\varnothing D_{\{Y_1\}}D_{\boldsymbol{Y}}}+\frac1{D_\varnothing D_{\{Y_2\}}D_{\boldsymbol{Y}}}\right)
\end{aligned}
```

For $\ell = 1$, $\boldsymbol{Y}=\{Y_1,Y_2,Y_3\}$:
```math
\begin{aligned}
\prod_{i=1}^{3}\Delta_{y_i}\left[\frac{1}{D}\right]
&=
\frac{1}{D_\varnothing}
-\frac{1}{D_{\{Y_1\}}}
-\frac{1}{D_{\{Y_2\}}}
-\frac{1}{D_{\{Y_3\}}}
+\frac{1}{D_{\{Y_1,Y_2\}}}
+\frac{1}{D_{\{Y_1,Y_3\}}}
+\frac{1}{D_{\{Y_2,Y_3\}}}
-\frac{1}{D_{\boldsymbol{Y}}}
\\
&=
y_1y_2y_3\left(
\frac{1}{D_\varnothing D_{\{Y_1\}}D_{\{Y_1,Y_2\}}D_{\boldsymbol{Y}}}
+\frac{1}{D_\varnothing D_{\{Y_1\}}D_{\{Y_1,Y_3\}}D_{\boldsymbol{Y}}}
\right.
\\
&\hspace{1.8cm}
+\frac{1}{D_\varnothing D_{\{Y_2\}}D_{\{Y_1,Y_2\}}D_{\boldsymbol{Y}}}
+\frac{1}{D_\varnothing D_{\{Y_2\}}D_{\{Y_2,Y_3\}}D_{\boldsymbol{Y}}}
\\
&\hspace{1.8cm}
\left.
+\frac{1}{D_\varnothing D_{\{Y_3\}}D_{\{Y_1,Y_3\}}D_{\boldsymbol{Y}}}
+\frac{1}{D_\varnothing D_{\{Y_3\}}D_{\{Y_2,Y_3\}}D_{\boldsymbol{Y}}}
\right)
\end{aligned}
```
