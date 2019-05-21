# Proofs of equivalences between Allen operators

These files contain proofs about some equivalences between Allen formulas.
They allow to express the Allen-logic operators in terms of a minimal core
set of operators, consisting in: either:
- `since(p,q)` and `until(p,q)` (proofs in equiv_until.v)
- `holds(p,q)` and `delay[1](p)` (proofs in equiv_holds.v)

The proofs are formalized in first order intuitionistic logic with the Coq proof
assistant. You can therefore use the Coq tool to mechanically check them. For
that, you need to have Coq installed (https://coq.inria.fr).

## Definitions

This section gives formal definitions of all the Allen operators.
Each Allen operators takes a fixed number of (0 or more) operand signals, and
a(nother) fixed number of (0 or more) parameters.

A *signal* is a boolean function of time.
The time domain is the set of natural numbers, starting with 0.
Signals can be also viewed as sets of disjoint, non-adjacent intervals,
also called *states*: the time intervals where the value of the signal is 1.

Boolean operators are defined as functions:

    All t . (p & q)(t) <-> p(t) & q(t)
    All t . (p | q)(t) <-> p(t) | q(t)
    All t . (~p)(t) <-> ~(p(t))

Other Allen operators are defined in the set-theoretic notation, as follows.

    up(p) = {[t,t+1) | [t,t’) in p & t > 0}
    dn(p) = {[t’,t’+1) | [t,t’) in p & t' < Inf}
    delay<T>(s)={[t+T,t'+T) | Ex [t,t') in s}  // We consider that Inf + T = Inf

    occurs(p,q) = {[t,t’) in q | Ex t'' in [t,t’) . p(t'')}
    holds(p,q) = {[t,t’) in q | All t'' in [t,t’) . p(t'')}

    meets(p,q) = {[t,t’) in p | Ex [t’,t’') in q}
    met(p,q) = {[t,t’) in p | Ex [t’’,t) in q}
    eq(p,q) = {[t,t’) in p | Ex [t,t’) in q}
    starts(p,q) = {[t,t’) in p | Ex [t,t’') in q . t’ < t''}
    started(p,q) = {[t,t’) in p | Ex [t,t’') in q . t’’ < t'}
    ends(p,q) = {[t,t’) in p | Ex [t'’,t') in q . t’’ < t}
    ended(p,q) = {[t,t’) in p | Ex [t'’,t') in q . t < t''}
    overlaps(p,q) = {[t,t’) in p | Ex [t’',t’'') in q . t < t’’ < t’ < t’''}
    overlapped(p,q) = {[t,t’) in p | Ex [t'’,t’'') in q . t’’ < t < t’’’ < t'}
    during(p,q) = {[t,t’) in p | Ex [t'’,t’'') in q . t’’ < t < t’ < t’''}
    contains(p,q) = {[t,t’) in p | Ex [t'’,t'’') in q . t < t’’ < t’’’ < t'}

    over(p,q) = {[t’’,t’) | [t,t’) in p & Ex [t’',t’'') in q . t < t’’ < t’ < t’''}

Temporal logic operators from future/past LTL are also defined as functions:

* until: (NB: [x,x) is considered empty)

    All t . (p U q)(t) <-> Ex t’>=t . q(t') & All t’’ in [t, t’) . p(t'’)

* since:

    All t . (p S q)(t) <-> Ex t’<=t . q(t’) & All t’’ in (t’,t] . p(t’')

* weak until:

    All t . (p W q)(t) <-> (p U q)(t) | All t’>=t . p(t’)

* weak since:

    All t . (p Z q)(t) <-> (p S q) | All t’<=t . p(t’)

Finally, some comparison operators are defined on top of LTL operators,
to explicit their goal. Assuming that, at time t, p=q=1, all these operators compare
which of p and q has started or will finish first. Conditions about the
past are prefixed with 'b' (for backward), conditions about the future
are prefixed with 'f' (for forward). Right means that the second argument
starts/finishes first; left means that the first argument starts/finishes
first. Eq indicates a non-strict comparison (e.g. flefteq). Finally,
lowercase operators use weak versions of Since/Until; capitalized operators
use strong versions of Since/Until.

    frighteq(p,q) = p W ~q   # forward right
    flefteq(p,q) = frighteq(q,p)
    feq(p,q) = flefteq(p,q) & frighteq(p,q)
    fleft(p,q) = flefteq(p,q) & ~frighteq(p,q)
    fright(p,q) = frighteq(p,q) & ~flefteq(p,q)

    Frighteq(p,q) = p U ~q
    Flefteq(p,q) = Frighteq(q,p)
    Feq(p,q) = Flefteq(p,q) & Frighteq(p,q)

    brighteq(p,q) = p Z ~q
    blefteq(p,q) = brighteq(q,p)
    beq(p,q) = blefteq(p,q) & brighteq(p,q)
    bleft(p,q) = blefteq(p,q) & ~brighteq(p,q)
    bright(p,q) = brighteq(p,q) & ~blefteq(p,q)

    Brighteq(p,q) = p S ~q
    Blefteq(p,q) = Brighteq(q,p)
    Beq(p,q) = Blefteq(p,q) & Brighteq(p,q)

    occurred(p,q) = q S (p & q)
    possible(p,q) = q U (p & q)

## Equivalences with Since & Until.
NB: These definitions exactly correspond to the proofs in equiv_until.v:

    during(p,q) =  bleft(p,q) & p & q & fleft(p,q)
    ends(p,q) = bleft(p,q) & p & q & feq(p,q)
    starts(p,q) = beq(p,q) & p & q & fleft(p,q)
    eq(p,q) = beq(p,q) & p & q & feq(p,q)
    over(p,q) = bright(p,q) & p & q & fleft(p,q)
    overlaps(p,q) = p U over(p,q)
    overlapped(p,q) = p S over(q,p)
    started(p,q) = p S starts(q,p)
    ended(p,q) = p U ends(q,p)
    _x(p,q) = p & ~q & Feq(p,~q)
    x_(p,q) = Beq(~p,q) & ~p & q
    meets(p,q) = p U _x(p,q)
    met(p,q) = p S x_(q,p)
    contains(p,q) = p U during(q,p) | p S during(q,p)
    holds(p,q) = brighteq(p,q) & p & q & frighteq(p,q)
    occurs(p,q) = possible(p,q) | occurred(p,q)

NB: The definitions above of the Allen operators can be simplified
by inlining the comparison operators (f|b)(left|right)(eq)?, leading
to a more compact (but arguably less readable) library, which exactly
corresponds to the version presented in the paper
"Scaling up RV-based Activity Detection":

    during(p,q) = p & q & ~wsince(p, ~q) & ~wuntil(p, ~q)
    ends(p,q) = p & q & ~wsince(p, ~q) & wuntil(p, ~q) & wuntil(q, ~p)
    starts(p,q) = p & q & wsince(p, ~q) & wsince(q, ~p) & ~wuntil(p, ~q)
    eq(p,q) = p & q & wsince(p, ~q) & wsince(q, ~p) & wuntil(p, ~q) & wuntil(q, ~p)
    over(p,q) = p & q & ~wsince(q, ~p) & ~wuntil(p, ~q)
    overlaps(p,q) = until(p, over(p,q))
    overlapped(p,q) = since(p, over(q,p))
    started(p,q) = since(p, starts(q,p))
    ended(p,q) = until(p, ends(q,p))
    meets(p,q) = until(p, p & ~q & until(p, q) & until(~q, ~p))
    met(p,q) = since(p, ~q & p & since(p,q) & since(~q,~p))
    contains(p,q) = let d = during(q,p) in until(p, d) | since(p, d)
    holds(p,q) = p & q & wsince(p, ~q) & wuntil(p, ~q)
    occurs(p,q) = q & ~holds(~p, q)

## Equivalences with holds & delay

The following equivalences express the main Allen operators in terms of `holds` and `delay[1]`.
The corresponding proofs can be found in the Coq files (extension .v) in this directory.

    occurs(p,q) = q & ~holds(~p,q)
    init(p) = p & ~met(p, ~p)
    final(p) = occurs(holds(p, delay<1>(p)), p)

    dn(p) = ~p & delay<1>(p)
    up(p) = dn(~p)
    met(p,q) = occurs(dn(q) & up(p), p)

    eq(p,q) = holds(p,q) & holds(q,p)
    over(p,q) =
      let s = up(q) & p & ~up(p) in
      let q1 = occurs(s,q) in
      let q2 = occurs(~p,q1) in   // overlapped(q,p)
      let q3 = occurs(s,p&q)
      q2 & q3
    overlapped(p,q) = occurs(over(q,p),p)
    overlaps(p,q) = occurs(over(p,q),p)
    starts(p,q) = # Aternative definition, w/o over
      let s = up(p) & up(q)
      let p1 = occurs(s,p)
      let q1 = occurs(s,q)
      let q2 = occurs(~p,q1)
      p1 & q2 | init(p) & init(q) & occurs(~p,q)
    started(p,q) = occurs(starts(q,p),p)
    ends(p,q) = over(q,~q|p) & ~over(q,p) | final(p) & final(q) & occurs(~p,q)
    ended(p,q) = occurs(ends(q,p),p)
    meets(p,q) = ~final(p) & (ends(p,~q) | eq(p,~q) | ended(p,~q))
    during(p,q) =
      let s = up(p) & q & ~up(q)
      let p1 = occurs(s,p)
      let p2 = occurs(~q,p1)   // overlapped(p,q)
      let p3 = p1 & ~p2   // during(p,q) | ends(p,q)
      p3 & ~ends(p,q)
    contains(p,q) = occurs(during(q,p),p)
