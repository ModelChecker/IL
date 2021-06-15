### General Design Philosophy

<!--
Extension the SMT-LIB language with new commands to define and verify systems.


Each system definition
* is parametrized by a state signature, a sequence of sorted variables
* can contain internal state variables;
* is hierarchical: may include (λ applications) instances of previously defined systems as subsystems;
* may be associated to (proved) state invariants (one-state properties) and transition invariants (two-properties);
* may be abstracted by its associated properties.


Formally, a transition system is a predicate _S_ of the form

_S = λ **i**:**δ**, **o**:**τ**, **s**:**σ** (I[**s**],T[**i**,**o**,**s**,**s'**])_

where

* _**i** = (i<sub>1</sub>, ..., i<sub>m</sub>)_ is a tuple of _input variables_ of respective type _**δ** = (δ<sub>1</sub>, ..., δ<sub>m</sub>,)_

* _**s** = (s<sub>1</sub>, ..., s<sub>n</sub>)_ and _**s** = (s<sub>1</sub>, ..., s<sub>n</sub>)_ are two tuples of _state variables_ of respective type _**σ** = (σ<sub>1</sub>, ..., σ<sub>n</sub>)_

* _**i** = (i<sub>1</sub>, ..., i<sub>k</sub>)_ is a tuple of _output variables_ of respective type _**τ** = (τ<sub>1</sub>, ..., τ<sub>k</sub>,)_

* _I_ is the system's _initial state condition_ expressed as an SMT-LIB formula over the state variables **s**.

* _T_ is the system's _transition relation_ expressed as an SMT-LIB formula over the input variables **i**, output variables **o**,  state variables **s**, and _next_ state variables **o**.

### Supported SMT-LIB commands

<tt>(declare-sort _s n_)</tt>

<tt>(declare-enum-sort _s_ (_c<sub>1</sub> ⋅⋅⋅ c<sub>n</sub>_))</tt>

<tt>(define-sort _s_ (_u<sub>1</sub> ⋅⋅⋅ u<sub>n</sub>_) _τ_)</tt>
  
<tt>(declare-const _c σ_)</tt>

<tt>(define-fun _f_ ((_x<sub>1</sub> σ<sub>1</sub>_) ··· (_x<sub>n</sub> σ<sub>n</sub>_)) _σ  t_)</tt>
-->


### System definition command

<tt>(define-system _S_</tt><br>
<tt>&nbsp; ((_i<sub>1</sub> δ<sub>1</sub>_)  ⋅⋅⋅ (_i<sub>m</sub> δ<sub>m</sub>_)) ; input vars </tt><br>
<tt>&nbsp; ((_o<sub>1</sub> τ<sub>1</sub>_) ⋅⋅⋅ (_o<sub>n</sub> τ<sub>n</sub>_)) ; output vars</tt><br>
<tt>&nbsp; ((_s<sub>1</sub> σ<sub>1</sub>_) ⋅⋅⋅ (_s<sub>p</sub> σ<sub>p</sub>_)) ; current state vars</tt><br>
<tt>&nbsp; (_sub<sub>1</sub> ⋅⋅⋅ sub<sub>k</sub>_) ; subsystems</tt><br>
<tt>&nbsp;&nbsp; _I_ &nbsp;&nbsp; ; initial state condition</tt><br>
<tt>&nbsp;&nbsp; _T_ &nbsp;&nbsp; ; transition relation</tt><br>
<tt>)</tt>

where

* _S_ is the system's identifier;
* each _i<sub>i</sub>_ is an input variable of sort _δ<sub>i</sub>_;
* each _o<sub>i</sub>_ is an output variables of sort _τ<sub>i</sub>_;
* each _s<sub>i</sub>_ is a current state variables of sort _σ<sub>i</sub>_;
* the system's next state variables are not provided explicitly but are denoted by convention as primed version of the current state variables (_s<sub>i</sub>'_ for each _s<sub>i</sub>);
* each _sub<sub>i</sub>_ has the form <tt>(_S<sub>i</sub>_ (_x<sub>1</sub> ⋅⋅⋅ x<sub>m<sub>i</sub></sub>_)) (_y<sub>1</sub> ⋅⋅⋅ y<sub>n<sub>i</sub></sub>_))</tt> where each _x_ is a variable of _S_ and each _y_ is a next state or an output variable of _S_ [to double check].

* _I_ is an SMT-LIB formula over the current state variables;
* _T_ is an SMT-LIB formula over all of the system's variables.


#### Requirements on _I_ and _T_

1. _I_ should denote a non-empty set of states.

2. _T_ should denote a right-total relation over states that also imposes no constraints on the value of the input variables.

A necessary and sufficient condition for (1) is that _I_ is satisfiable (in the relevant background theory).
A sufficient condition for (2) is that _T_ is the the following formula is valid (in the relevant theory): 

_∀ i<sub>1</sub> ⋅⋅⋅ ∀ i<sub>m</sub> ∀ s<sub>1</sub> ⋅⋅⋅ ∀ s<sub>q</sub> ∃ o<sub>1</sub> ⋅⋅⋅ ∃ o<sub>n</sub> ∃ s<sub>1</sub>' ⋅⋅⋅ ∃ s<sub>q</sub>' T_



