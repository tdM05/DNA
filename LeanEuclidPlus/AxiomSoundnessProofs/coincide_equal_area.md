# coincide_equal_area

$M = \mathbb{R}^2$.

## 1. Interpretation of the symbols

- **Point** $:= \mathbb{R}^2$.
- **Line** $L$ $:=$ zero set of an affine form $\ell_L(p) = n\cdot p - k$, $n \neq 0$; $\ \texttt{onLine}\ p\ L := \ell_L(p) = 0$.
- **Circle** $\gamma := (o, \rho)$, $\rho > 0$; $\ \texttt{onCircle}\ p\ \gamma := \|p - o\|^2 = \rho^2$.
- $\texttt{distinctPointsOnLine}\ a\ b\ L := \ell_L(a)=0 \wedge \ell_L(b)=0 \wedge a \neq b$.
- $\texttt{sameSide}\ a\ b\ L := \ell_L(a)\cdot\ell_L(b) > 0$.
- $\texttt{area}(\texttt{ofPoints}\ a\ b\ c) := \operatorname{vol}\big(\operatorname{disk}(o,\rho) \cap H\big)$, where $\gamma=(o,\rho)$ is the circle through $a,b,c$ and $H = \{p : \ell_{ac}(p)\cdot\ell_{ac}(b) \ge 0\}$ the closed half-plane of chord $ac$ on $b$'s side (and $:= 0$ if $a,b,c$ are collinear / not concyclic).

## 2. Soundness

Assume $\texttt{coincides}$: there are $c,e,d,f,CD,\gamma=(o,\rho)$ with $c,d,e,f \in \gamma$, $\texttt{distinctPointsOnLine}\ c\ d\ CD$, $e,f \notin CD$, and $\ell_{CD}(e)\cdot\ell_{CD}(f) > 0$. Must show $\texttt{area}(\texttt{ofPoints}\ c\ e\ d) = \texttt{area}(\texttt{ofPoints}\ c\ f\ d)$.

$c,d,e$ are non-collinear ($e \notin CD = \operatorname{line}(c,d)$), so their circle is $\gamma$ and their chord line is $CD$; same for $c,f,d$. Hence

$$\texttt{area}(\texttt{ofPoints}\ c\ e\ d) = \operatorname{vol}\big(\operatorname{disk}(o,\rho) \cap H_e\big), \qquad \texttt{area}(\texttt{ofPoints}\ c\ f\ d) = \operatorname{vol}\big(\operatorname{disk}(o,\rho) \cap H_f\big),$$

with $H_e = \{p : \ell_{CD}(p)\cdot\ell_{CD}(e) \ge 0\}$, $H_f = \{p : \ell_{CD}(p)\cdot\ell_{CD}(f) \ge 0\}$. Since $\ell_{CD}(e), \ell_{CD}(f)$ have the same sign, $H_e = H_f$, so the two regions are identical and their volumes are equal. $\blacksquare$
