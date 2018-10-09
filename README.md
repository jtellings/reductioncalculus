# Reduction calculus for <a href="http://dx.doi.org/10.1007/s10988-005-6920-7" target="_blank">Moschovakis (2006)</a>

<a href="http://www.math.ucla.edu/~ynm/" target="_blank">Moschovakis</a> (<a href="http://dx.doi.org/10.1007/s10988-005-6920-7" target="_blank">2006</a>) presents a view of meanings in natural language as abstract algorithms. A reduction calculus is given that reduces a standard LF into an algorithm. This script performs the reduction, which is tedious to do by hand. Each reduction step is displayed separately. In addition to the calculus described in the paper, this script also handles intensional anaphora.

Example for 'John loves Mary and he knows it':
    <pre>
**LF 1: and(loves(John, Mary), knows(he, that it))**
What does 'it' refer to? Type 'i' for intensional.
_i loves(John, Mary)_
What does 'he' refer to? Type 'i' for intensional.
_John_

and(loves(P0, Mary), knows(P0, that $p))
 where {P0 := John,
        $p := fint(loves(John, Mary))}

_==> (intensional); Lemma_
(and(loves(P0, Mary), knows*(P0, P3, P4, P5)) where {P0 := John})
 where {P5 := lambda p0 p (Mary),
        P4 := lambda p0 p (John),
        P3 := lambda p0 p (loves(p, p0))}

_==> (hr)_
and(loves(P0, Mary), knows*(P0, P3, P4, P5))
 where {P0 := John,
        P5 := lambda p0 p (Mary),
        P4 := lambda p0 p (John),
        P3 := lambda p0 p (loves(p, p0))}

_==> (ap)_
(and(loves(P0, Mary), P6) where {P6 := knows*(P0, P3, P4, P5)})
 where {P4 := lambda p0 p (Mary),
        P3 := lambda p0 p (loves(p, p0)),
        P0 := John,
        P5 := lambda p0 p (John)}

[... 5 more steps ...]

_==> (BS)_
and(P7, P6)
 where {P4 := lambda p0 p (Mary),
        P6 := knows*(P0, P3, P4, P5),
        P8 := Mary,
        P7 := loves(P0, P8),
        P3 := lambda p0 p (loves(p, p0)),
        P0 := John,
        P5 := lambda p0 p (John)}

</pre>

See [manual](manual.pdf) for more details.
