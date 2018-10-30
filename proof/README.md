# Proofs of equivalences between Allen operators

These files contain proofs about some equivalences between Allen formulas.
They allow to express the main Allen operators in terms of a minimal core set of operators,
consisting in: `holds(p,q)` and `delay[1](p)`.

The proofs are formalized in first order intuitionisting logic with the Coq proof assistant.
You can therefore use the Coq tool to mechanically check them.

## Definitions

This section gives formal definitions of all the Allen operators.
Each Allen operators takes a fixed number of (0 or more) operand signals, and
a(nother) fixed number of (0 or more) parameters.

A *signal* is a boolean function of time.
The time domain is the set of natural numbers, starting with 0.
Signals can be also viewed as sets of disjoint, non-adjacent intervals,
also called *states*: the time intervals where the value of the signal is 1.

A few Allen operators are defined in the function notation, as follows.

    All t . (p & q)(t) = p(t) & q(t)
    All t . (p | q)(t) = p(t) | q(t)
    All t . (~p)(t) = ~(p(t))

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

## Equivalences

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
