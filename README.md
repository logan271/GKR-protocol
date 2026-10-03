# How the GKR protocol works

GKR is an interactive protocol for checking a claimed circuit output. This overview shows the full flow before we unpack the wiring and the algebra one step at a time.

```text
Public to the verifier: circuit and input
Prover evaluates the circuit and claims its output
                         │
                         ▼
Verifier randomizes the output claim
to get one claim about the output layer
                         │
                         ▼
┌──────────── One layer transition ────────────┐
│                                              │
│  Run one complete, multi-round sum-check     │
│    Prover sends a polynomial for this round  │
│    Verifier checks degree and endpoints      │
│    Verifier sends a fresh random challenge   │
│    Repeat for each child-label coordinate    │
│                                              │
│  Final check uses the circuit's wiring       │
│  and leaves TWO claims about the next layer  │
│                                              │
│  Prover gives a polynomial along a line      │
│  Verifier checks both endpoints, then picks  │
│  a random point on that line                 │
│  The two claims fold into ONE new claim      │
└──────────────────────┬───────────────────────┘
                       │
                       ▼
             One claim at the next layer
                       │
                       └──── Start a new complete
                             sum-check for the next
                             layer transition

                       ⋮

At the input layer, the verifier evaluates the
known input's multilinear extension directly
                       │
                       ▼
              Accept if every check passed
```

**The two loops are different:** each layer transition contains several sum-check rounds; after those rounds and line reduction finish, GKR advances by one circuit layer and begins a new sum-check.

In Section 4.6.4 of *Proofs, Arguments, and Zero-Knowledge*, `add_i` and `mult_i` describe **the circuit's wiring**. They tell us which gates are connected and which operation to apply. They do not contain the values flowing through those gates.

The book calls the multiplication predicate `mult_i`; it is the same thing we previously called `mul_i`.

## 1. Their arguments are gate addresses

Both functions take three gate labels: $\mathrm{add}_i(a,b,c)$ and $\mathrm{mult}_i(a,b,c)$.

- `a` identifies a gate in layer `i`.
- `b` identifies its proposed first input gate in layer `i + 1`.
- `c` identifies its proposed second input gate in layer `i + 1`.

Remember that GKR numbers layers backward: the output is layer zero, and the input is the last layer. Gate `a` reads values from the next numbered layer.

The functions answer yes/no questions. $\mathrm{add}_i(a,b,c)=1$ exactly when gate $a$ is an addition gate whose first and second inputs are gates $b$ and $c$. Likewise, $\mathrm{mult}_i(a,b,c)=1$ exactly when gate $a$ is a multiplication gate with those ordered inputs. Otherwise, the answer is zero.

**A label is an address, not a value.** If gate `01` currently holds the number `7`, its label is still `01`.

If layer `i` has `2^k_i` gates, its labels have `k_i` bits. Thus the three arguments together have `k_i + 2*k_(i+1)` bits. This explains the domain written in the book.

## 2. A concrete circuit

Suppose two gates in layer `i` read four gates from layer `i + 1`:

```text
Layer i+1:    00: 2    01: 3        10: 5   11: 7
                 \      /              \      /
Layer i:          0: +                  1: ×
                  value 5               value 35
```

Each label before a colon is a gate address. Each number after a colon in the input layer is a gate value.

The wiring predicates have exactly these nonzero entries:

$$
\mathrm{add}_i(0,00,01)=1,
\qquad
\mathrm{mult}_i(1,10,11)=1.
$$

Every other entry is zero:

| Query | Result | Reason |
|---|---:|---|
| `add_i(0, 00, 01)` | 1 | Correct addition gate and children |
| `add_i(0, 00, 10)` | 0 | Wrong second child |
| `mult_i(0, 00, 01)` | 0 | Gate 0 performs addition |
| `mult_i(1, 10, 11)` | 1 | Correct multiplication gate and children |

We fix an ordering for the two input wires. Even though addition and multiplication are commutative, we do not also mark the reversed pair as valid. Doing so would double-count the gate's contribution in the sum below.

If the input values change, the gate values change, but **these wiring predicates stay exactly the same**. They depend only on the public circuit structure.

## 3. Why encode wiring this way?

Recall that $W_i(a)$ means the value stored at gate $a$ in layer $i$.

The wiring predicates let us express any gate's value using one uniform formula. Sum over every ordered pair of child labels $(b,c)$:

$$
\begin{aligned}
W_i(a)=\sum_{b,c}\Bigl[
&\mathrm{add}_i(a,b,c)
  \bigl(W_{i+1}(b)+W_{i+1}(c)\bigr)\\
+{}&\mathrm{mult}_i(a,b,c)
  W_{i+1}(b)W_{i+1}(c)
\Bigr].
\end{aligned}
$$

The sum ranges over all Boolean gate labels `b` and `c` in layer `i + 1`.

It appears to consider many irrelevant gate pairs. But the predicates act as **selectors**: multiplying by zero removes every irrelevant term.

For gate $a=0$, only the addition term with $(b,c)=(00,01)$ survives:

$$W_i(0)=1\cdot(2+3)=5. $$

For gate $a=1$, only the multiplication term with $(b,c)=(10,11)$ survives:

$$W_i(1)=1\cdot5\cdot7=35. $$

**This is the key transformation: the circuit's gate operations become a sum.** That puts them in a form sum-check can handle.

## 4. What do the tildes mean?

### A “table” is a function's list of inputs and outputs

For a function whose inputs are bit strings, we can list its output for every possible input. That list is its **table of values**, much like a truth table. The outputs can be any field elements; they do not have to be bits.

For example, the function `W_i` in our circuit has this complete table:

| Input: gate label `a` | Output: `W_i(a)` |
|---|---:|
| `0` | 5 |
| `1` | 35 |

Writing `[5, 35]` is shorthand for this table, with the inputs ordered as `0, 1`.

The function `add_i` has a different table. Its input is a triple of labels, and its output is a bit:

| Input: `(a, b, c)` | Output: `add_i(a,b,c)` |
|---|---:|
| `(0, 00, 00)` | 0 |
| `(0, 00, 01)` | 1 |
| `(0, 00, 10)` | 0 |
| `(0, 00, 11)` | 0 |
| … | … |
| `(1, 11, 11)` | 0 |

There are `2 × 4 × 4 = 32` possible inputs, so the full table has 32 rows. Only `(0, 00, 01)` has output one. Likewise, `mult_i` has its own 32-row table, with a one only at `(1, 10, 11)`.

Each triple can also be viewed as a single five-bit string. For example, `(0, 00, 01)` is `00001`. Thus a “Boolean point” here means an assignment of zero or one to each of those five address bits.

**These tables describe functions; they need not be stored explicitly.** An implementation can compute `add_i(a,b,c)` by looking up gate `a`'s operation and two input addresses in the circuit description.

### An extension represents those same rows with a polynomial

The original functions accept only bit strings. Sum-check also needs evaluations at arbitrary field points, whose coordinates need not be zero or one.

A function's **multilinear extension** is the unique polynomial, over the chosen field, that matches every row of its table and has degree at most one in each input coordinate. For a table $f:\lbrace 0,1 \rbrace^k\to\mathbb F$, the extension is:

$$
\widetilde f(r)=\sum_{x\in\lbrace 0,1 \rbrace^k}f(x) \chi_x(r),
\qquad
\chi_x(r)=\prod_{j=1}^k\bigl(x_jr_j+(1-x_j)(1-r_j)\bigr).
$$

The factor $\chi_x$ selects the row labeled $x$: at Boolean input $r=x$, it equals one, while at every other Boolean input it equals zero.

Start with the two-row $W_i$ table $[5,35]$. Its extension is:

$$
\widetilde W_i(t)=5(1-t)+35t,
\qquad
\widetilde W_i(0)=5,
\quad
\widetilde W_i(1)=35.
$$

It preserves both original outputs and also defines an output at every other field element. The restriction to degree at most one makes this extension unique; without a degree restriction, many polynomials could match those two rows.

For the wiring tables, we do the same thing with five variables, one per address bit. We are **extending the function's domain**, not changing its answers on the original Boolean inputs.

The book denotes these extensions by a tilde:

$$
\widetilde{\mathrm{add}}_i,
\qquad
\widetilde{\mathrm{mult}}_i.
$$

We can write them explicitly for our example. Let $A$ be the one-bit current-layer address, $B=(B_1,B_2)$ the first child address, and $C=(C_1,C_2)$ the second child address.

$$
\begin{aligned}
\widetilde{\mathrm{add}}_i(A,B,C)
  &=(1-A)(1-B_1)(1-B_2)(1-C_1)C_2,\\
\widetilde{\mathrm{mult}}_i(A,B,C)
  &=A B_1(1-B_2)C_1C_2.
\end{aligned}
$$

Each factor checks one bit:

- To select a bit equal to zero, use `(1-X)`.
- To select a bit equal to one, use `X`.

For example, the addition expression selects the five-bit tuple `0 00 01`. At that tuple every factor is one. At any other Boolean tuple, at least one factor is zero.

This construction generalizes: build one such selector polynomial for every valid wiring tuple and add them together.

**Outside the Boolean domain, the extensions need not return zero or one.** They are algebraic interpolations of the wiring tables, not literal yes/no predicates at those points.

## 5. The gate-value identity at a random point

The wiring equation was first described for one Boolean gate label. GKR also needs it at a random field point. Fix any $r\in\mathbb F^{k_i}$ and sum over Boolean child labels $b,c$:

$$
\begin{aligned}
\widetilde W_i(r)=\sum_{b,c\in\lbrace 0,1 \rbrace^{k_{i+1}}}\Bigl[{}
&\widetilde{\mathrm{add}}_i(r,b,c)
  \bigl(W_{i+1}(b)+W_{i+1}(c)\bigr)\\
+{}&\widetilde{\mathrm{mult}}_i(r,b,c)
  W_{i+1}(b)W_{i+1}(c)
\Bigr].
\end{aligned}
$$

The child labels in this sum are Boolean, so $W_{i+1}(b)$ and $W_{i+1}(c)$ are ordinary table entries. The wiring predicates select the valid child pair for each Boolean gate address. Both sides are multilinear in $r$ and agree at every Boolean $r$, so they agree at every field point.

For the tiny example with two gates in layer $i$ and values $5,35$, write the one-bit address as $r$. The addition gate's extension contributes weight $1-r$ and the multiplication gate's extension contributes weight $r$:

$$
\widetilde W_i(r)=(1-r)(2+3)+r(5\cdot7)=5(1-r)+35r.
$$

This is the multilinear extension of the value table $[5,35]$. The verifier can now begin from a random-point claim about the entire layer, rather than opening a separate claim for every gate.

## 6. Where sum-check enters

GKR repeats a **complete sum-check protocol once per layer transition**. Each invocation contains many sum-check rounds; the rounds are not the layer transitions. It is also not one sum-check run for every gate. At the start of layer $i$, the verifier has one claim for the whole layer:

$$
\widetilde W_i(r_i)=h_i,
\qquad r_i\in\mathbb F^{k_i}.
$$

Usually $r_i$ is random. The claim concerns the multilinear extension of the whole layer's value table. The verifier does not know the intermediate gate values, so it cannot calculate the left side directly.

### Set up this layer's sum-check

The identity above says that $h_i$ equals a sum over pairs of child-gate labels. Freeze the current-layer point $r_i$, and define a polynomial in the child-label variables $B,C$:

$$
\begin{aligned}
f_i(B,C)={}&\widetilde{\mathrm{add}}_i(r_i,B,C)
  \bigl(\widetilde W_{i+1}(B)+\widetilde W_{i+1}(C)\bigr)\\
&+\widetilde{\mathrm{mult}}_i(r_i,B,C)
  \widetilde W_{i+1}(B)\widetilde W_{i+1}(C).
\end{aligned}
$$

Each of $B,C$ has $k_{i+1}$ coordinates, so this polynomial has $m=2k_{i+1}$ variables. The claim for this layer is now the standard sum-check statement:

$$
h_i=\sum_{B,C\in\lbrace 0,1 \rbrace^{k_{i+1}}}f_i(B,C).
$$

The sum ranges over Boolean child labels. During sum-check, challenges bind some coordinates to arbitrary field elements. Each individual variable of $f_i$ has degree at most two: the wiring extension has degree one in that coordinate, and a child-value extension contributes at most one more. The verifier knows this degree bound even though it does not know the next layer's value table.

This gives the round count for **one** layer transition. If layer $i+1$ has $2^{k_{i+1}}$ gates, a child label has $k_{i+1}$ bits. A pair of child labels therefore has $m=2k_{i+1}$ bits, so this sum-check has $2k_{i+1}$ rounds. In each round, one of those child-label bits is fixed to a fresh field challenge.

### The messages and checks, round by round

Flatten the coordinates of $B,C$ into $X_1,\ldots,X_m$, and call the resulting polynomial $f(X_1,\ldots,X_m)$. Let the verifier's current claimed sum be $h_0=h_i$.

**Round 1.** Before seeing any challenges for this sum-check, the prover sends the univariate polynomial

$$
q_1(T)=\sum_{x_2,\ldots,x_m\in\lbrace 0,1 \rbrace}
f(T,x_2,\ldots,x_m).
$$

Only the first child-label bit is left symbolic; the prover sums over all Boolean settings of the other bits. The honest prover can do this because it evaluated the circuit and knows the complete layer $i+1$ value table, the circuit wiring, and the fixed point $r_i$.

The verifier checks the degree and the endpoints:

$$
\deg(q_1)\le 2,
\qquad q_1(0)+q_1(1)=h_0.
$$

The endpoint sum partitions the Boolean cube into cases where the first bit is zero and one. If either check fails, the verifier rejects. Otherwise, it samples a fresh uniform $s_1\in\mathbb F$, sends it to the prover, and sets the new claimed sum to $h_1=q_1(s_1)$.

**Round 2.** After receiving $s_1$, the prover sends

$$
q_2(T)=\sum_{x_3,\ldots,x_m\in\lbrace 0,1 \rbrace}
f(s_1,T,x_3,\ldots,x_m).
$$

The verifier checks $\deg(q_2)\le2$ and

$$
q_2(0)+q_2(1)=h_1=q_1(s_1).
$$

If those checks pass, it samples a fresh $s_2\in\mathbb F$ and sets $h_2=q_2(s_2)$.

**Round $j$.** After challenges $s_1,\ldots,s_{j-1}$, the honest prover sends

$$
q_j(T)=\sum_{x_{j+1},\ldots,x_m\in\lbrace 0,1 \rbrace}
f(s_1,\ldots,s_{j-1},T,x_{j+1},\ldots,x_m).
$$

The verifier checks $\deg(q_j)\le2$ and that the two endpoints add to the previous claimed value. It then samples $s_j$ and sets $h_j=q_j(s_j)$. At every round, one more coordinate is fixed, reducing the number of remaining Boolean summands by half.

The challenge comes after that round's polynomial message. This order matters: the prover must commit to a low-degree polynomial before it knows the random point at which that polynomial will be tested.

### What does the prover actually send?

A degree-at-most-two univariate polynomial is determined by its values at three distinct field points. The prover can therefore send three evaluations rather than symbolic coefficients. The verifier interpolates the polynomial, checks the degree bound, and obtains its endpoint values. This is the general degree-plus-one representation used in the sum-check description.

The honest prover computes each required evaluation by substituting the selected value of $T$, summing over all remaining Boolean assignments, and evaluating the terms using its known next-layer values and wiring. It performs the sum; it does not need to send the whole layer table.

Before the last round, the verifier needs only the current claimed sum, the degree bound, and the polynomial message to check the endpoint relation. It does not need to know the coefficients or evaluate the large sum itself.

### The final round: check the polynomial against the circuit

There are $m=2k_{i+1}$ rounds in this layer's sum-check. After the verifier samples $s_m$, no Boolean variables remain. It now needs to check

$$
q_m(s_m)=f_i(b^{\ast},c^{\ast}),
$$

where $(b^{\ast},c^{\ast})=(s_1,\ldots,s_m)$ split into the first and last $k_{i+1}$ coordinates. These are random field vectors, not necessarily Boolean gate labels.

The verifier knows the public circuit and can evaluate the wiring extensions at $(r_i,b^{\ast},c^{\ast})$. It does not know the next layer's gate-value polynomial at $b^{\ast}$ and $c^{\ast}$, so the prover supplies claimed values

$$
z_1=\widetilde W_{i+1}(b^{\ast}),
\qquad z_2=\widetilde W_{i+1}(c^{\ast}).
$$

The verifier substitutes these into the definition of $f_i$ and checks:

$$
q_m(s_m)=
\widetilde{\mathrm{add}}_i(r_i,b^{\ast},c^{\ast})(z_1+z_2)
+\widetilde{\mathrm{mult}}_i(r_i,b^{\ast},c^{\ast})z_1z_2.
$$

This is the final evaluation check for this sum-check invocation. It ties the transcript to the circuit's wiring relation. The verifier still has not established that $z_1,z_2$ really are evaluations of the next layer's table; it carries those claims into the next layer's iteration.

### Why a false claim is caught

If the starting claim $h_i$ is false, the prover cannot send the correct first partial-sum polynomial: its endpoint values would add to the true sum, not $h_i$. Any polynomial it sends to preserve the false claim differs from the correct one. Once the message is fixed, a fresh random challenge hits a root of their difference with probability at most $2/|\mathbb F|$, because the difference has degree at most two.

If the lie survives a round, the verifier now has a false claim with one fewer Boolean variable, and the same reasoning applies. Across $m$ rounds, the sum-check error is at most $2m/|\mathbb F|$. Line reduction and subsequent layer iterations contribute additional soundness error.

### What one layer transition accomplishes

At the start, there is one claim about the current layer:

$$
\widetilde W_i(r_i)=h_i.
$$

After sum-check and its final evaluation check, there are two claims about the next layer:

$$
\widetilde W_{i+1}(b^{\ast})=z_1,
\qquad
\widetilde W_{i+1}(c^{\ast})=z_2.
$$

The line-reduction step combines these two claims into one claim at a fresh point of layer $i+1$. Only after that reduction is complete does GKR start a **new, full sum-check invocation** for the transition from layer $i+1$ to layer $i+2$.

The protocol is nested in this order:

1. For the transition from layer $i$ to layer $i+1$, run a complete sum-check. Its rounds fix the child-label bits one by one.
2. The final sum-check check leaves two evaluation claims about layer $i+1$.
3. Apply line reduction to combine those into one claim about layer $i+1$.
4. Start a new complete sum-check for the next layer transition.

In short: **sum-check rounds fix the coordinates of child labels; a completed sum-check plus line reduction advances the claim by one circuit layer.** At the final input layer, the verifier evaluates the input's multilinear extension directly instead of starting another sum-check.

## 7. Line reduction: fold two claims into one

After the layer's sum-check, the verifier has two claims about the next layer's multilinear extension:

$$
\widetilde W_{i+1}(b^{\ast})=z_1,
\qquad
\widetilde W_{i+1}(c^{\ast})=z_2,
$$

where $b^{\ast},c^{\ast}\in\mathbb F^{k_{i+1}}$ are the two random points left by sum-check. The next layer's protocol is easiest to run with a **single** claim. Line reduction turns these two claims into one.

### 1. Draw a line through the two points

There is a unique line parametrization that starts at $b^{\ast}$ when $t=0$ and reaches $c^{\ast}$ when $t=1$:

$$
\ell(t)=b^{\ast}+t(c^{\ast}-b^{\ast}),
\qquad
\ell(0)=b^{\ast},\quad \ell(1)=c^{\ast}.
$$

### 2. The prover describes the extension along that line

The prover sends a univariate polynomial $q(t)$, claiming it is the next layer's multilinear extension restricted to the line:

$$
q(t)=\widetilde W_{i+1}(\ell(t)).
$$

Why is this univariate polynomial low degree? The multilinear extension has degree at most one in each of its $k_{i+1}$ coordinates. Along a line, each coordinate is an affine function of $t$. Multiplying at most one such factor per coordinate gives total degree at most $k_{i+1}$ in $t$. The verifier checks this degree bound.

### 3. Check that the line polynomial matches both claims

The verifier checks the endpoints:

$$
q(0)=z_1,
\qquad q(1)=z_2.
$$

These checks ensure the supplied line polynomial passes through the two values from the sum-check. They do not by themselves prove it is the true restriction of $\widetilde W_{i+1}$; a false polynomial could still pass through those endpoints.

### 4. Pick a fresh point and keep just one claim

After receiving $q$, the verifier samples a fresh uniform $s\in\mathbb F$. The next claim is:

$$
\widetilde W_{i+1}(\ell(s))=q(s).
$$

This is one evaluation claim at one point of the next layer. The next layer's GKR iteration checks it. If $q$ is not the true restriction, its difference from the true line polynomial is nonzero and has degree at most $k_{i+1}$. It can vanish at at most $k_{i+1}$ field points, so the random $s$ catches a false restriction except with probability at most $k_{i+1}/|\mathbb F|$.

The roles are worth separating: the sum-check has already checked the wiring relation at its final random point, using the two claimed child values. Line reduction then compresses those two child-value claims into one claim that can be passed to the next layer.

### A one-coordinate example

Suppose the next layer has two gate values, $[5,35]$, so its multilinear extension is $\widetilde W(t)=5+30t$. Take two sum-check points $b^{\ast}=2$ and $c^{\ast}=4$ in $\mathbb F_{101}$. The true endpoint values are $65$ and $24$ (since $125\equiv24\pmod{101}$).

In one dimension, the line from $2$ to $4$ is $\ell(t)=2+2t$. The prover's correct line polynomial is:

$$
q(t)=\widetilde W(2+2t)=65+60t\pmod{101}.
$$

It passes the endpoint checks: $q(0)=65$ and $q(1)=24$. If the verifier samples $s=7$, the one claim passed forward is:

$$
\widetilde W(16)=q(7)=81\pmod{101},
$$

because $\ell(7)=16$. GKR now checks this one claim in the next layer's iteration.

### The repeating GKR rhythm

For every non-input layer, the pattern is:

1. Start with one claim about this layer.
2. Run a complete, multi-round sum-check for this layer transition.
3. Finish with two claims about the next layer.
4. Use line reduction to combine them into one claim about that next layer.
5. Start a new complete sum-check for the next transition.

At the input layer, there is no next transition: the verifier evaluates the known input's multilinear extension directly and checks the last claim.

## Keep these three roles separate

| Function | What it encodes | Depends on input values? |
|---|---|---|
| `W_i(a)` | The value of gate `a` | Yes |
| `add_i(a,b,c)` | Whether this is a valid addition connection | No |
| `mult_i(a,b,c)` | Whether this is a valid multiplication connection | No |



The wiring predicates supply the algebraic relationship between adjacent layers. Sum-check lets GKR verify that relationship without checking each gate separately.

Reference: [*Proofs, Arguments, and Zero-Knowledge*, Section 4.6.4](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf).
