---
title: Model Checking Intermediate Language
author: Cesare Tinelli 
date: 2022-06-27
---

# Model Checking Intermediate Language (Draft)

The Model Checking Intermediate Language (IL, for short) is an intermediate language 
meant to be a common input and output standard for model checker 
for finite- and infinite-state systems, 
with an initial focus is on finite-state ones.

## General Design Philosophy

IL has been designed to be general enough to be an intermediate target language 
for a variety of user-facing specification languages for model checking.
At the same time, IL is meant to be simple enough to be easily compilable 
to lower level languages or be directly supported by model checking tools based 
on SAT/SMT technology. 

For being an intermediate language, models expressed in IL are meant 
to be produced and processed by tools, hence it was designed to have

* simple, easily parsable syntax;
* a rich set of data types;
* minimal syntactic sugar, at least initially;
* well-understood formal semantics;
* a small but comprehensive set of commands;
* simple translations to lower level modeling languages such as Btor2 and Aiger.

Based on these principles, IL provides no direct support for many of the features 
offered by current hardware modeling languages such as VHDL and Verilog 
or more general purpose system modeling languages 
such as SMV, TLA+, PROMELA, Simulink, SCADE, Lustre. 
However, it strives to offer enough capability so that problems expressed 
in those languages can be reduced to problems in IL.

IL is an extension the [SMT-LIB language](https://smtlib.cs.uiowa.edu/language.shtml) 
with new commands to define and verify systems.
It allows the definition of multi-component synchronous or asynchronous reactive systems.
It also allows the specification and checking of reachability conditions 
(or, indirectly state and transition invariants) and deadlocks, 
possibly under fairness conditions on input values. 

IL assumes a discrete and linear notion of time and hence has a standard trace-based semantics.

Each system definition:
* defines a _transition system_ via the use of SMT formulas, 
  imposing minimal syntactic restrictions on those formulas;
* is parametrized by a _state signature_, a sequence of typed variables;
* partitions state variables into input, output and local variables;
* can be expressed as the synchronous or asynchronous composition of other systems 
* is _hierarchical_ ,i.e., may include (instances of) previously defined systems as subsystems;
* can encode both synchronous and asynchronous system composition.

The current focus on _finite-state_ systems. 
However, the language has been designed to support the specification 
of infinite-state system as well.

## Technical Preliminaries

The base logic of IL is the same as that of SMT-LIB: 
many-sorted first-order logic with equality and let binders.
We refer to this logic simply as FOL.
When we say _formula_, with no further qualifications, we refer to an arbitrary formula 
of FOL (possibly with quantifiers and let binders).

We say that a formula is _quantifier-free_ if it contains no occurrences 
of the quantifiers $\forall$ and 
$\exists$.
We say that it is _binder-free_ if it is quantifier-free and also contains no occurrences
of the let binder.

The _scope_ of binders and the notion of _free_ and _bound_ (occurrences of) variables 
in a formula are defined as usual.

#### Notation
If $F$ is a formula and 
$\boldsymbol{x} = (x_1, \ldots, x_n)$ a tuple of distinct variables, 
we write $F[\boldsymbol{x}]$ or $F[x_1, \ldots, x_n]$ to express the fact that every variable 
in $\boldsymbol{x}$ is free in $F$ (although $F$ may have additional free variables).
We write $\boldsymbol{x},\boldsymbol{y}$ to denote the concatenation of tuple 
$\boldsymbol{x}$ with tuple $\boldsymbol{y}$.
When its clear from the context, given a formula $F[\boldsymbol{x}]$ and 
a tuple $\boldsymbol{t} = (t_1, \ldots, t_n)$ of terms of the same type 
as $\boldsymbol{x} = (x_1, \ldots, x_n)$, 
we write $F[\boldsymbol{t}]$ or $F[t_1, \ldots, t_n]$ to denote the formula obtained from $F$ 
by simultaneously replacing each occurrence of $x_i$ by $t_i$ for all $i=1,\ldots,n$.

A formula may contain _uninterpreted_ constant and function symbols, 
that is, symbols with no constraints on their interpretation. 
For most purposes, we treat uninterpreted constants as free variables and 
treat uninterpreted function symbols as _second-order_ free variables.

### Transition systems

Formally, a transition system $S$ is a pair of predicates of the form

$$S = ( 
   I_S [\boldsymbol i, \boldsymbol o,  \boldsymbol s],~
   T_S [\boldsymbol i, \boldsymbol o, \boldsymbol s, \boldsymbol{i'}, \boldsymbol{o'}, \boldsymbol{s'}] 
)$$

where

* $\boldsymbol i$ and $\boldsymbol{i'}$ are two tuples of _input variables_ 
  with the same length and type;
* $\boldsymbol o$ and $\boldsymbol{o'}$ are two tuples of _output variables_ 
  with the same length and type;
* $\boldsymbol s$ and $\boldsymbol{s'}$ are two tuples of _local variables_ 
  with the same length and type;
* $I_S$ is the system's _initial state condition_, expressed as a formula 
  with no (free) variables from $\boldsymbol{i'},\boldsymbol{o'},\boldsymbol{s'}$;
* $T_S$ is the system's _transition condition_, expressed as a formula 
  over the variables 
  $\boldsymbol{i},\boldsymbol{o},\boldsymbol{s},\boldsymbol{i'},\boldsymbol{o'},\boldsymbol{s'}$.

**Note:** 
For convenience, but differently from other formalizations, a (full) state of system $S$
is expressed by a valuation of the variables $\boldsymbol{i},\boldsymbol{o},\boldsymbol{s}$.
In other words, input and output variables are automatically _stateful_ since the transition relation formula can access old values of inputs and outputs in addition to the old values 
of the local state. 
This means that, technically, $S$ is a closed system. 
The designation of some state variables as input or output is, however, important 
when combining systems together, to capture which of the state values are shared 
between two systems being combined, and how.

**Note:** Similarly to Mealy machines, the initial state condition is also meant to specify 
the initial system's output based on the initial state and input. 
Correspondingly, the transition relation is also meant to specify the system's output 
in every later state of the computation.

**Note:** The input and output values corresponding to the transition to the new state are 
those in the variables $\boldsymbol{i'}$ and 
$\boldsymbol{o'}$. 
The values of $\boldsymbol{i}, \boldsymbol{o}$ are the _old_ input and output values.

### Trace Semantics

A transition system in the sense above implicitly defines a model
(i.e., a Kripke structure) of First-Order Linear Temporal Logic (FO-LTL).

The language of FO-LTL extends that of FOL with the same modal operators of time
as in standard (propositional) LTL: 
$\mathbf{always},$
$\mathbf{eventually},$
$\mathbf{next},$
$\mathbf{until},$
$\mathbf{release}$.
For our purposes of defining the semantics of transition systems
it is enough to consider just the $\mathbf{always}$ and
$\mathbf{eventually}$ operators.

The non-temporal operators depend on the particular theory, in the sense of SMT, 
considered (linear integer/real arithmetic, bit vectors, strings, and so on, and 
their combinations).
The meaning of theory symbols (such as arithmetic operators) and theory sorts
(such as $\mathsf{Int}$,
$\mathsf{Real},$
$\mathsf{Array(Int, Real)},$ 
$\mathsf{BitVec(3)}$, $\ldots$) 
is fixed by the theory $\mathcal T$ in question. 
Once a theory $\mathcal T$ has been fixed then, the meaning of a FO-LTL formula $F$ 
is provided by an interpretation of the uninterpreted (constant and function) symbols 
of $F$, if any,
as well as an infinite sequence of valuations for the free variables of $F$.

More precisely, we will fix a tuple $\boldsymbol x = (x_1,\ldots,x_n)$ 
of distinct _state_ variables, meant to represent the state of a computation system. 
We will denote by $\boldsymbol{x'}$ 
the tuple $(x_1',\ldots,x_n')$ 
and write formulas of the form $F[\boldsymbol f, \boldsymbol x, \boldsymbol x']$ 
where $\boldsymbol f$ is a tuple of uninterpreted symbols.
If $F$ has free occurrences of variables 
of $\boldsymbol x$ 
but not of $\boldsymbol{x'}$ we call it a _one-state_ formula; 
otherwise, we call it a _two-state_ formula.

A _valuation of_ $\boldsymbol x$, 
or a _state over_ $\boldsymbol x$, is function mapping 
each variable $x$ in $\boldsymbol x$ 
to a value of $x$'s type.
Let $\kappa$ be a positive ordinal smaller than 
$\omega$, the cardinality of the natural numbers.
A _trace (of length_ $\kappa$_)_ is 
any state sequence $\pi = (s_j  \mid 0 \leq j < \kappa)$.
Note that $\pi$ is the finite sequence $s_0, \ldots, s_{\kappa-1}$
when $\kappa < \omega$ and 
is the infinite sequence $s_0, s_1, \ldots$ otherwise.
For all $i$ with $0 \leq i < \kappa$ , 
we denote by $\pi[i]$ the state $s_i$ and
by $\pi^i$ the subsequence 
$(s_j \mid i \leq j < \kappa)$.


### Infinite-Trace Semantics

Let $F[\boldsymbol f, \boldsymbol x, \boldsymbol{x'}]$ be a formula as above.
If $\mathcal I$ is an interpretation
of $\boldsymbol{f}$ 
in the theory $\mathcal T$ and 
$\pi$ is an infinite trace,
then $(\mathcal I, \pi)$ _satisfies_ $F$, 
written $(\mathcal I, \pi) \models F$, iff

* $F$ is atomic and
  $\mathcal{I}[\boldsymbol x \mapsto \pi[0](\boldsymbol x),\boldsymbol{x'} \mapsto \pi[1](\boldsymbol x)]$
  satisfies $F$ as in FOL;
* $F = \lnot G~$ and 
  $~(\mathcal I, \pi) \not\models G$;
* $F = G_1 \land G_2~$ and 
  $~(\mathcal I, \pi) \models G_i$ for $i=1,2$;
* $F = \exists x\, G$ and
  $(\mathcal I[z \mapsto v], \pi) \models G$ for some value $v$ for $x$;
* $F = \mathbf{eventually}~G$ and 
  $(\mathcal I, \pi^i) \models G$ for some $i \geq 0$;
* $F = \mathbf{always}~G$ and
  $(\mathcal I, \pi^i) \models G$ for all $i \geq 0$.
<!-- * $(\mathcal I, \pi^1) \models G$ when $F = \mathbf{next}~G$; -->

The semantics of the propositional connectives $\lor, \rightarrow, \leftrightarrow$
and the quantifier $\forall$
can be defined by reduction to the connectives above 
(e.g., by defining $G_1 \lor G_2$ as 
$\lnot(\lnot G_1 \land \lnot G_2)$ and so on).
Note that $\exists$ is a _static_, or _rigid_, quantifier:
the meaning of the variable it quantifies does not change over time,
that is, from state to state in $\pi$.
The same is true for uninterpreted symbols. 
They are _rigid_ in the same sense: their meaning does not change over time.

Another way to understand the difference between rigid and non-rigid symbols is that 
state variables are mutable over time 
whereas quantified variables, theory symbols and uninterpreted symbols are all immutable.

Now let
$S = ( 
   I_S [\boldsymbol i, \boldsymbol o,  \boldsymbol s],~
   T_S [\boldsymbol i, \boldsymbol o, \boldsymbol s, \boldsymbol{i'}, \boldsymbol{o'}, \boldsymbol{s'}] 
)$
be a transition system with state variables $\boldsymbol i, \boldsymbol o,  \boldsymbol s$.

The _infinite trace semantics_ of $S$ is the set of all pairs $(\mathcal I, \pi)$ 
of interpretations $\mathcal I$ in $\mathcal T$ and infinite traces $\pi$ such that

$$(\mathcal I, \pi) \models
  I_S \land\ \mathbf{always}~T_S
$$

We call any such pair an _execution_ of $S$.

**Note:**
[We focus on reactive systems]


### Finite-Trace Semantics

Let $F[\boldsymbol f, \boldsymbol x, \boldsymbol{x'}]$, $\mathcal I$, $\mathcal T$ and $\pi$ 
be defined is in the subsection above.
For every $n \geq 0$, $(\mathcal I, \pi)$ _$n$-satisfies_ $F$, 
written $(\mathcal I, \pi) \models_n F$, iff

* $F$ is atomic and
  $\mathcal I[\boldsymbol x \mapsto \pi[0](\boldsymbol x), 
              \boldsymbol{x'} \mapsto \pi[1](\boldsymbol x)]$ satisfies $F$ as in FOL;

* $F = \lnot G$ and $(\mathcal I, \pi) \not\models_n G$ 

* $F = G_1 \land G_2$ and $(\mathcal I, \pi) \models_n G_i$ for $i=1,2$;

* $F = \exists x\, G$ and $(\mathcal I[z \mapsto v], \pi) \models_n G$ for some value $v$ for $x$;

* $F = \mathbf{eventually}~G$ and $(\mathcal I, \pi^i) \models_{n-i} G$ for some $i = 0, \ldots, n$;

* $F = \mathbf{always}~G$ and $(\mathcal I, \pi^i) \models_{n-i} G$ for all $i = 0, \ldots, n$;


The semantics of the propositional connectives $\lor, \rightarrow, \leftrightarrow$
and the quantifier $\forall$
is again defined by reduction to the connectives above. 

Intuitively, $n$-satisfiability specifies when a formula is true over
the first $n$ states of a trace.
Note that this notion is well defined even when $n=0$ regardless of whether $F$ 
has free occurrences of variables from $\boldsymbol{x'}$ or not.
In the atomic case, this is true because $\pi$, for being an _infinite_ trace,
does contain the state $\pi[1]$.
In the general case, the claim can be shown by a simple inductive argument.

The notion of $n$-satisfiability is useful when one is interested, as we are,
in state reachability.
The reason is that a state satisfying a (non-temporal) property $P$ is reachable 
in a system $S$ 
if and only if the temporal formula $\mathbf{eventually}~P$ is $n$-satisfied 
by an execution of $S$ for some $n$.


## Supported SMT-LIB commands

SMT-LIB is a command-based language with LISP-like syntax designed to be 
a common input/output language for SMT solvers.

IL adopts the following SMT-LIB commands:

* <tt>(declare-sort $s$ $n$)</tt>

  Declares $s$ to be a sort symbol (i.e., type constructor) of arity $n$.
  Examples:
  ```scheme
  (declare-sort A 0)
  (declare-sort Set 1)
  ; possible sorts: A, (Set A), (Set (Set A)), ...
  ```

* <tt>(define-sort $s$ ($u_1 \cdots u_n$) $\tau$)</tt>

  Defines _s_ as synonym of a parametric type _τ_ with parameters _u<sub>1</sub> ⋅⋅⋅ u<sub>n</sub>_.
  Examples:
  ```scheme
  (declare-sort NestedSet (X) (Set (Set X)))
  ; possible sorts: (NestedSet A), ...
  ```

* <tt>(declare-const _c σ_)</tt>

  Declares a constant _c_ of sort _σ_.
  Examples:
  ```scheme
  (declare-const a A)
  (declare-const n Int)
  ```

* <tt>(define-fun _f_ ((_x<sub>1</sub> σ<sub>1</sub>_) ··· (_x<sub>n</sub> σ<sub>n</sub>_)) _σ  t_)</tt>

  Defines a (non-recursive) function _f_ with inputs _x<sub>1</sub>_, ..., _x<sub>n_ 
  (of respective sort _σ<sub>1</sub>_, ..., _σ<sub>n</sub>_), output sort _σ_, and body _t_.

* <tt>(set-logic _L_)</tt>

  Defines the model's _data logic_, that is, the background theories of relevant datatypes
  (e.g., integers, reals, bit vectors, and so on) as well as the language of allowed logical constraints 
  (e.g., quantifier-free, linear, etc.).

One addition to SMT-LIB is the binary symbol `!=` for disequality.
For each term `s` and `t` of the same sort, `(!= s t)` has the same meaning as `(not (= s t))` or, equivalently, `(distinct s t)`.

## IL-specific commands

### Enumeration declaration

<tt>(declare-enum-sort _s_ (_c<sub>1</sub> ⋅⋅⋅ c<sub>n</sub>_))</tt>

Declares _s_ to be an enumerative type with (distinct) values _c<sub>1</sub>_, ..., _c<sub>n</sub>_.

### System definition command

<tt>(define-system _S_</tt><br>
<tt>&nbsp; :input ((_i<sub>1</sub> δ<sub>1</sub>_)  ⋅⋅⋅ (_i<sub>m</sub> δ<sub>m</sub>_))</tt><br>
<tt>&nbsp; :output ((_o<sub>1</sub> τ<sub>1</sub>_) ⋅⋅⋅ (_o<sub>n</sub> τ<sub>n</sub>_))</tt><br>
<tt>&nbsp; :local ((_s<sub>1</sub> σ<sub>1</sub>_) ⋅⋅⋅ (_s<sub>p</sub> σ<sub>p</sub>_))</tt><br>
<!-- <tt>&nbsp; :sub (_sub<sub>1</sub> ⋅⋅⋅ sub<sub>k</sub>_) ; subsystems</tt><br> -->
<tt>&nbsp; :init (_I<sub>1</sub> ⋅⋅⋅ I<sub>q</sub>_)</tt><br>
<tt>&nbsp; :trans (_T<sub>1</sub> ⋅⋅⋅ T<sub>r</sub>_)</tt><br>
<tt>&nbsp; :inv (_P<sub>1</sub> ⋅⋅⋅ P<sub>s</sub>_)</tt><br>
<tt>)</tt>


where

* _S_ is the system's identifier;
* each _i<sub>j</sub>_ is an _input_ variable of sort _δ<sub>j</sub>_;
* each _o<sub>j</sub>_ is an _output_ variable of sort _τ<sub>j</sub>_;
* each _s<sub>j</sub>_ is a _local_ variable of sort _σ<sub>j</sub>_;
* each _i<sub>j</sub>_, _o<sub>j</sub>_, _s<sub>j</sub>_ denote _current-state_ values
* _next-state variables_ are not provided explicitly but are denoted by convention appending ' to the names of the current-state variables _i<sub>j</sub>_, _o<sub>j</sub>_, and _s<sub>j</sub>_;
* each _I<sub>j</sub>_ is an SMT-LIB formula over the input, output and current-state variables or a _system application_ that expresses a constraint on the initial states of _S_; 
* each _T<sub>j</sub>_ is an SMT-LIB formula over all of the system's variables or a _system application_ that expresses a constraint on the state transitions of _S_;
* each _P<sub>j</sub>_ is an SMT-LIB formula over all of the _unprimed_ system's variables that expresses a constraint on all reachable states of _S_;
* a system application has the form (_S<sub>i</sub>_ _x<sub>i<sub>1</sub></sub> ⋅⋅⋅ x<sub>i<sub>m</sub></sub> y<sub>i<sub>1</sub></sub> ⋅⋅⋅ y<sub>i<sub>n</sub></sub>_) where _S<sub>i<sub>_ is a system other than _S_ with <sub>i<sub>m</sub></sub> inputs and <sub>i<sub>n</sub></sub> outputs, and each _x_ is a variable of _S_ and each _y_ is a local or output variable of _S_.


The various aspects of the system are provided as SMT-LIB attribute-value pairs. The order of the attributes can be arbitrary but each attribute can occur at most once.  A missing attribute stands for a default value: the empty list <tt>()</tt>. The sequence of formulas in the <tt>:init</tt> (resp., <tt>:trans</tt> and <tt>:inv</tt>) attribute is to be understood conjunctively. 

#### Semantics

Formally, the system _S_ specified with a `define-system` is the pair

_S = ( λ**i**:**δ** λ**o**:**τ** I<sub>S</sub>[**i**,**o**,**s**], λ**i**:**δ** λ**i'**:**δ** λ**o**:**τ** λ**o'**:**τ** T<sub>S</sub>[**i**,**o**,**s**,**i'**,**o'**,**s'**] )_

defining a transitions system with initial state condition _I<sub>S</sub>_ and transition relation _T<sub>S</sub>_ where

* _I<sub>S</sub> = I<sub>1</sub> ∧ ⋅⋅⋅ ∧ I<sub>q</sub> ∧ P<sub>1</sub> ∧ ⋅⋅⋅ ∧ P<sub>s</sub>_;

* _T<sub>S</sub> = T<sub>1</sub> ∧ ⋅⋅⋅ ∧ T<sub>r</sub> ∧ (P<sub>1</sub> ∧ ⋅⋅⋅ ∧ P<sub>s</sub> )[**i** ↦ **i'**, **o** ↦ **o'**, **s** ↦ **s'**]_;

* If _I<sub>i</sub>_ is the application (S<sub>i</sub> **x**<sub>i</sub> **y**<sub>i</sub>), it is syntactic sugar for the formula _fresh(fst(S<sub>i</sub>) **x**<sub>i</sub> **y**<sub>i</sub>)_;

* If _T<sub>i</sub>_ is the application (S<sub>i</sub> **x**<sub>i</sub> **y**<sub>i</sub>), it is syntactic sugar for the formula _fresh(snd(S<sub>i</sub>) **x**<sub>i</sub> **x'**<sub>i</sub> **y**<sub>i</sub> **y'**<sub>i</sub>)_;

* _fst_ in the first projection over pairs and _snd_ is the second;

* for any formula _F_,  the expression _fresh(F)_ denotes the formula obtained from _F_ by replacing each free variable of _F_ by a fresh variable.

**Notes:** 
* The full set _**s**_ of local variables of _S_ is (recursively) the disjoint union of the variables declared in the <tt>:local</tt> attribute together with the local variables of all the systems applied in <tt>:init</tt> or <tt>:trans</tt>.

* The order of the formulas in <tt>:init</tt>, <tt>:trans</tt> and   <tt>:inv</tt> attributes does not matter.

* _T<sub>S</sub>_ is not required to be functional over inputs and current state, thus allowing the modeling of non-deterministic systems.

##### Trace Semantics 

Let's extend the syntax and the semantics of (first-order) LTL to allow primed stated variables in formulas, interpreting them over a trace as the value they have in the second state of the trace.

Then, the set of traces defined by the transition system _(I<sub>S</sub>, T<sub>S</sub>)_ is exactly the set of traces that satisfy the LTL formula: _I<sub>S</sub>[**i**,**o**,**s**] ∧ **always** T<sub>S</sub>[**i**,**o**,**s**,**i'**,**o'**,**s'**]_.

> **Discussion:** Should we restrict the semantics to infinite traces only?  
>
> Since it is possible to define systems that have _deadlock_ states (reachable states with no successors, more precisely, reachable states falsifying the transition constraints), finite traces ending in a deadlock state have to be excluded from the semantics. In that case though, it is not possible to disprove safety properties by means of a finite counterexample trace because that trace may not extend to an infinite trace of the system.
>
> In contrast, allowing finite traces as well in the semantics has the problem that ...
> 




##### Sanity requirements on _I<sub>S</sub>_ and _T<sub>S</sub>_

One way to address the deadlock state problem is to consider only infinite traces in the semantics (systems that are meant to reach a final state can be always modeled with states that cycle back to themselves and produce stuttering outputs).
In that semantics, the reachability of a deadlock state (a state with no successors in the transition relation) indicates an error in the system's definition.

Intuitively, for a system definition to define a system with no deadlocks:

1. Any assignment of values to the input variables can be extended to a total assignment (to all the unprimed variables) that satisfies _I<sub>S</sub>_.

2. For any reachable state _s_, any assignment to the primed input variables can be extended to a total assignment _s'_ so that _s,s'_ satisfies _T<sub>S</sub>_.


The first restriction above guarantees that the system can start at all. The second ensures that from any reachable state and for any new input the system can move to another state (_and so_ also produce output).

* A sufficient condition for (1) is that the following formula is valid in the (previously specified) background theory:  _∀ **i** ∃ **o** ∃ **s** I<sub>S</sub>_

* A sufficient condition for (2) is that the following formula is valid in the background theory: _∀ **i** ∀ **o** ∀ **s** ∀ **i'** ∃ **o'** ∃ **s'** T<sub>S</sub>_
 
  This condition is not necessary, however, since it need not apply to unreachable states. Let _Reachable[**i**, **o**, **s**]_ denote the (possibly higher-order) formula satisfied exactly by the reachable states of _S_. Then, a more accurate sufficient condition for (2) above would be the validity of the formula:

  _∀ **i** ∀ **o** ∀ **s** ∀ **i'** ∃ **o'** ∃ **s'** (Reachable[**i**,**o**,**s**] ⇒ T<sub>S</sub>)_

**Note:** In general, checking the two sufficient conditions above automatically can be impossible or very expensive (because of the quantifier alternations in the conditions).


#### Examples, non-composite systems

(Adapted from "Principles of Cyber-Physical Systems" by R. Alur, 2015)

**Note:** When reading these examples, it is helpful to keep in mind that, intuitively, in the <tt>:init</tt> formulas the input values are given and the local and output values are to be defined with respect to them. In contrast, in the <tt>:trans</tt> formulas the new input values, and old input, output and local values are given, and the new local and output values are to be defined.


```scheme
; The output of Delay is initially 0 and then is the previous input.
; No local variable is needed
(define-system Delay
  :input ( (in Int) )
  :output ( (out Int) )
  :init ( 
    (= out 0)
  )
  :trans ( 
    ; the new output is the old input
    (= out' in)
  )
)

; The output of Delay2 is initially any number in [0,10] and then is its previous input.
(define-system Delay2
  :input ( (in Int) )
  :output ( (out Int) )
  :init (
    (<= 0 out 10) ; more than one possible initial output
  )
  :trans ( 
    (= out' in)
  )
)


(define-enum-sort LightStatus (on off))

; TimedSwitch models a timed light switch where the light stays
; on for at most 10 steps unless it is switched off before.
; The input Boolean is interpreted as an on or off command 
; depending on whether the light was respectively off or on.

; set-of-transitions-style definition
(define-system TimedSwitch1
  :input ( (press Bool) )
  :output ( (sig Bool) )
  :local ( (status LightStatus) (n Int) )
  :init ( 
    (= n 0)
    (ite press (= status on) (= status off))
    (= sig (= status on))
  )
  :trans (
    (= sig' (= status' on))
    (let ((stay-off (and (= status off) (not press') (= status' off) (= n' n)))
          (turn-on  (and (= status off) press' (= status' on) (= n' n)))
          (stay-on  (and (= status on) (not press') (< n 10) (= status' on) (= n' (+ n 1))))
          (turn-off (and (= status on) (or press' (>= n 10)) (= status' off) (= n' 0))) 
         )
     (or stay-off turn-on turn-off stay-on) 
    )
  )
)

; guarded-transitions-style definition
(define-system TimedSwitch2
  :input ( (press Bool) )
  :output ( (sig Bool) )
  :local ( (status LightStatus) (n Int) )
  :init ( 
    (= n 0)
    (ite press (= status on) (status off))
    (= sig (= status on))
  )
  :trans (
    (= sig' (= status' on))
    (=> (and (= status off) (not press')) 
        (and (= status' off) (= n' n)))
    (=> (and (= status off) press') 
        (and (= status' on) (= n' n)))
    (=> (and (= status on) (not press') (< 10 n))
        (and (= status' on) (= n' (+ n 1))))
    (=> (and (= status on) (or press' (>= n 10))) 
        (and (= status' off) (= n' 0)))
  )
)

(define-fun flip ((s LightStatus)) LightStatus
  (ite (= s off) on off) 
)

; equational-style definition
(define-system TimedSwitch3
  :input ( (press Bool) )
  :output ( (sig Bool) )
  :local ( (status LightStatus) (n Int) )
  :init ( 
    (= n 0)
    (= status (ite press on off))
    (= sig (= status on))
  )
  :trans (
    (= sig (= status' on))
    (= status' (ite press' (flip status)
                 (ite (= status off) off
                   (ite (< n 10) on off))))
    (= n' (ite (or (= status off) (status' off)) 0 
            (+ n 1)))
  )
)  


; `NonDetArbiter` grants input requests expressed by the (Boolean) event `req1` and `req2`.
; Initially, no requests are granted. Afterwards, a request is always granted (expressed 
; by issuing the event `gran1` or `grant2`), if it is the only request. 
; When both inputs contain a request, one of the two is granted, with a non-deterministic
; choice.
;
(define-system NonDetArbiter
  :input ( (req1 Bool) (req2 Bool) )
  :output ( (gran1 Bool) (gran2 Bool) )
  :local ( (s Bool) )
  :init ( (not gran1) (not gran2) )  ; nothing is granted initially
  :trans (
    (=> (and (not req1') (not req2'))
        (and (not gran1') (not gran2')))
    (=> (and req1' (not req2'))
        (and 'gran1 (not gran2')))
    (=> (and (not req1') req2')
        (and (not gran1') gran2'))
    (=> (and req1' req2')
        ; the unconstrained value of `s` is used as non-deterministic choice
        (ite s'
          (and gran1' (not gran2')
          (and (not gran1') gran2'))))
  ) 
)

; `DelayedArbiter` is similar to `NonDetArbiter` but grants requests a cycle later. 
(define-system DelayedArbiter
  :input ( (req1 Bool) (req2 Bool) )
  :output ( (gran1 Bool) (gran2 Bool) )
  :local ( (s Bool) )
  :init ( (not gran1) (not gran2) )  ; nothing is granted initially
  :trans (
    (=> (and (not req1) (not req2))
        (and (not gran1') (not gran2')))
    (=> (and req1 (not req2))
        (and gran1' (not gran2')))
    (=> (and (not req1) req2)
        (and (not gran1') gran2'))
    (=> (and req1 req2)
        ; the unconstrained value of `s` is used as non-deterministic choice
        (ite s
          (and gran1' (not gran2')
          (and (not gran1') gran2'))))
  ) 
)



; Events carrying data can be modeled as instances of the polymorphic algebraic datatype
; (Event X) where X is the type of the data carried by the event.

(declare-datatype Event (par (X)
  (none)
  (some (val X))
))

; Similar to `NonDetArbiter` but for requests expressed as integer events.
(define-system IntNonDetArbiter
  :input ( (req1 (Event Int)) (req2 (Event Int)) )
  :output ( (gran1 (Event Int)) (gran2 (Event Int)) )
  :local ( (s Bool) )
  :init ( (= gran1 gran2 none) )
  :trans (
    (=> (= req1' req2' none) 
        (= gran1' gran2' none))
    (=> (and (distinct req1' none) (= req2' none))
        (and (= gran1' req1) (= gran2' none)))
    (=> (and (= req1' none) (distinct' req2' none))
        (and (= gran1' none) (= gran2' req2')))
    (=> (and (distinct req1' none) (distinct req2' none))
        (ite s
          (and (= gran1' req1') (= gran2' none))
          (and (= gran1' none) (= gran2' req2'))))
  ) 
)

; An event-triggered channel that arbitrarily loses its input data
(define-system LossyIntChannel 
  :input ( (in (Event Int)) )
  :output ( (out (Event Int)) )
  :local ( (s Bool) )
  ; whether the input event is transmitted depends on s
  ; s is unconstrained so can take any value during execution
  :inv ( (= out (ite s in none)) )    
)

; A system that simply passes along the current input `in` when the `clock` input is true.
; When `clock` is false it outputs the value output the last time `clock` was true.
; Until `clock` is true for the first time it outputs the initial value of `init`.
(define-system StutteringClockedCopy 
  :input ( (clock Bool) (init Int) (in Int) )
  :output ( (out Int) )
  :init ( (ite clock (= out s in) (= out s init)) )
  :trans ( (ite clock (= out' s' in) (= out' s' s)) )
)
```

#### Examples, composite systems

Parallel composition is achieved by applying systems in initial state or transition conditions.

```scheme
;----------------
; Two-step delay
;----------------

;     +------------------------------------+
;     |   DoubleDelay                      |
;     |  +-----------+      +-----------+  |
;  in |  |           | temp |           |  | out
; ----+->|   Delay   |----->|   Delay   |--+---->
;     |  |           |      |           |  |
;     |  +-----------+      +-----------+  |
;     +------------------------------------+

; One-step delay
(define-system Delay
  :input ( (i Int) )
  :output ( (o Int) )
  :init  ( (= o 0) )
  :trans ( (= o' i) )
)

; Two-step delay
(define-system DoubleDelay
  :input ( (in Int) )
  :output ( (out Int) )
  :local ( (temp Int) )
  :init  ( (Delay in temp)  ; can be understood as a macro call that also adds state
           (Delay temp out) )
  :trans ( (Delay in temp) 
           (Delay temp out) )
)
;; DoubleDelay expanded
(define-system DoubleDelay
  :input ( (in Int) )
  :output ( (out Int) )
  :local ( (temp Int) ) 
  :init ( (= temp 0)   ; expansion of `(Delay in temp)`
          (= out 0)    ; expansion of `(Delay temp out)`
        )  
  )
  :trans ( (= temp' in)    ; expansion of `(Delay in temp)`
           (= out' temp)   ; expansion of `(Delay temp out)`
         )
)
; Example trace:
;   in = 1, 2, 3, 4, 5, 6, 7, ...
; temp = 0, 1, 2, 3, 4, 5, 6, ...
;  out = 0, 0, 1, 2, 3, 4, 5, ...


; 'Latch' has a Boolean state represented by state variable `s` with arbitrary initial value.
; A set request (represented by input `set` being true) sets the new value of `s` to true
; unless there is a concurrent reset request (represented by input `reset` being true). 
; In that case, the choice between the two requests is resolved arbitrarily. 
; In the absence of either a set or a reset, the value of `s` is unchanged.
; The initial value of output 'out' is arbitrary. Afterwards, it is the previous value of 's'.
;
(define-system Latch
  :input ( (set Bool) (reset Bool) )
  :output ( (out Bool) )
  :local ( (s Bool) )
  :trans (
    (= out' s)
    (=> (and (not set) (not reset)) (= s' s))
    (=> (and set (not reset)) (= s' true))
    (=> (and (not set) reset) (= s' false))
    ; when the old values of `set` and `reset` are both `true`,
    ; the new value of `s` is arbitrary
  )
)

; More compact, equational definition of Latch
(define-system Latch1
  :input ( (set Bool) (reset Bool) )
  :output ( (out Bool) )
  :local ( (b Bool) )  ; used for non-deterministic choice
  :trans (
    (= out' (or (and set (or (not reset) b))
                (and (not set) (not reset) out)))
  )
)


;---------------
; 3-bit counter
;---------------

; 'OneBitCounter' is a stateful 1-bit counter implemented using 
; the latch component modeled by `Latch`.
; The counter goes from 0 (represented as `false`) to 1 (`true`)
; with a carry value of 0, or from 1 to 0 with a carry value of 1 when
; the increment signal `inc` is true.
; It is reset to 0 (`false`) when the start signal is true.
; The initial value of the counter is arbitrary.

;        +------------------------------------------------------------+
;        |                                                            |
;        | +--------------------------------------------------------+ |
;        | |                                              +-------+ | |
;        +-|-----------------------------------|``-.  set |       | | |
;        | |                          |`-._    |    :---->|       | | |
;        | +->|``-.                +--|   _]o--|..-`      | Latch | | |
;        |    |    :--+----\``-.   |  |.-`          reset |       |-+-+--> out
;   inc -+----|..-`   |     )   :--+--------------------->|       |   |
;        |            | +--/..-`                          +-------+   |
;        |            | |                                             |
; start ----------------+                OneBitCounter                |
;        |            |                                               |
;        +------------+-----------------------------------------------+
;                     |     
;                     v carry

(define-system OneBitCounter
  :input ( (inc Bool) (start Bool) )
  :output ( (out Bool) (carry Bool) )
  :local ( (set Bool) (reset Bool) )
  :init (
    (Latch set reset out)
    (= set (and inc (not reset)))
    (= reset (or carry start))
    (= carry (and inc out))
  )
  :trans (
    (Latch set reset out)
    (= set' (and inc' (not reset')))
    (= reset' (or carry' start'))
    (= carry' (and inc' out'))
  )
)

; a more concise version
(define-system OneBitCounter
  :input ( (inc Bool) (start Bool) )
  :output ( (out Bool) (carry Bool) )
  :local ( (set Bool) (reset Bool) )
  :inv ( 
     ; _one-state_ constraints asserted for every state
     (= set (and inc (not reset)))
     (= reset (or carry start))
     (= carry (and inc out))
  )
  :init (
    (Latch set reset out)
  )
  :trans (
    (Latch set reset out)
  )
)

; an even more concise version
(define-system OneBitCounter
  :input ( (inc Bool) (start Bool) )
  :output ( (out Bool) (carry Bool) )
  :local ( (set Bool) (reset Bool) )
  :inv ( 
     ; _one-state_ constraints asserted for every state
     (= set (and inc (not reset)))
     (= reset (or carry start))
     (= carry (and inc out))
  )
  :compose ( ; new attribute
    ; application below is implicitly added to both :init and :trans
    (Latch set reset out) 
  )
)


; 'ThreeBitCounter' implements a 3-bit resettable counter
; by cascading three 1-bit counters. 
; The output is three Boolean values standing for the three bits, 
; with out0 being the least significant one.
;
(define-system ThreeBitCounter
  :input ( (inc Bool) (start Bool) )
  :output ( (out0 Bool) (out1 Bool) (out2 Bool) )
  :local ( (car0 Bool) (car1 Bool) (car2 Bool) )
  :init (
    (OneBitCounter inc start out0 car0) 
    (OneBitCounter car0 start out1 car1)
    (OneBitCounter car1 start out2 car2) 
  )
  :trans (
    (OneBitCounter inc start out0 car0) 
    (OneBitCounter car0 start out1 car1)
    (OneBitCounter car1 start out2 car2) 
  )
)

; more concisely
define-system ThreeBitCounter
  :input ( (inc Bool) (start Bool) )
  :output ( (out0 Bool) (out1 Bool) (out2 Bool) )
  :local ( (car0 Bool) (car1 Bool) (car2 Bool) )
  :compose (
    (OneBitCounter inc start out0 car0) 
    (OneBitCounter car0 start out1 car1)
    (OneBitCounter car1 start out2 car2) 
  )
)

```

### System verification command

<tt>(check-system _S_</tt>
<tt>&nbsp; :input ((_i<sub>1</sub> δ<sub>1</sub>_)  ⋅⋅⋅ (_i<sub>m</sub> δ<sub>m</sub>_))</tt>
<tt>&nbsp; :output ((_o<sub>1</sub> τ<sub>1</sub>_) ⋅⋅⋅ (_o<sub>n</sub> τ<sub>n</sub>_))</tt>
<tt>&nbsp; :local ((_s<sub>1</sub> σ<sub>1</sub>_) ⋅⋅⋅ (_s<sub>p</sub> σ<sub>p</sub>_))</tt>
<tt>&nbsp; :assumptions (_a<sub>1</sub> ⋅⋅⋅ a<sub>q</sub>_)</tt>
<tt>&nbsp; :fairness (_f<sub>1</sub> ⋅⋅⋅ f<sub>h</sub>_)</tt>
<tt>&nbsp; :reachable (_r<sub>1</sub> ⋅⋅⋅ r<sub>i</sub>_)</tt>
<tt>&nbsp; :invariants (_p<sub>1</sub> ⋅⋅⋅ p<sub>k</sub>_)</tt>
<tt>)</tt>

<!-- <tt>&nbsp; :conjectures (_c<sub>1</sub> ⋅⋅⋅ c<sub>j</sub>_)</tt> -->


where

* _S_ is the identifier of a previously defined system with _m_ inputs, _n_ outputs, and _p_ local variables;
* each _i<sub>j</sub>_ is a renaming of the corresponding input variable of _S_ of sort _δ<sub>i</sub>_;
* each _o<sub>j</sub>_ is a renaming of the corresponding output variable of _S_ of sort _τ<sub>i</sub>_;
* each _s<sub>j</sub>_ is a renaming of the corresponding local variable of _S_ of sort _σ<sub>i</sub>_;
* each _a<sub>j</sub>_ is a triple of the form <tt>(_n<sub>j</sub> l<sub>j</sub> A<sub>j</sub>_)</tt>  
  with <tt>_A<sub>j</sub>_</tt> a formula over input and local variables 
  (called _environmental assumption_);
* each _f<sub>j</sub>_ is a triple of the form <tt>(_n<sub>j</sub> l<sub>j</sub> F<sub>j</sub>_)</tt>
  with <tt>_F<sub>j</sub>_</tt> a formula over input, output and local variables
  (called _fairness condition_);
* each _r<sub>j</sub>_ is a triple of the form <tt>(_n<sub>j</sub> l<sub>j</sub> R<sub>j</sub>_)</tt>
  where <tt>_R<sub>j</sub>_</tt> is a formula over input, output and local variables
  (called _reachability condition_);
* each _p<sub>j</sub>_ is a triple of the form <tt>(_n<sub>j</sub> l<sub>j</sub> P<sub>j</sub>_)</tt>
  where <tt>_P<sub>j</sub>_</tt> is a formula over input, output and local variables
  (called _invariance condition_);
* each _n<sub>j</sub>_ is fresh identifier 
* each _l<sub>j</sub>_ is a string literal
* a formula is an (quantifier-free?) FOL formula over primed and unprimed variables 
<!-- * each _c<sub>j</sub>_ is a triple of the form <tt>(_n<sub>j</sub> l<sub>j</sub> C<sub>j</sub>_)</tt> -->
<!-- * each _C<sub>j</sub>_ is a formula over input, output and local variables; -->

**Note:** The ids _n<sub>j</sub>_ are meant to be user-defined names for the corresponding condition. The strings _n<sub>j</sub>_ are labels that can be attached for convenience, especially when producing output.


Let _I<sub>S</sub>_ and _T<sub>S</sub>_ be respectively the initial state condition and transition predicate of _S_.

Let _A = A<sub>1</sub> ∧ ⋅⋅⋅ ∧ A<sub>q</sub>_, _F = F<sub>1</sub> ∧ ⋅⋅⋅ ∧ F<sub>h</sub>_, _R = R<sub>1</sub> ∧ ⋅⋅⋅ ∧ R<sub>i</sub>_, _P = P<sub>1</sub> ∧ ⋅⋅⋅ ∧ P<sub>k</sub>_.

The command above succeeds if both the following holds:

1. there is a trace of _S_ that satisfies all the environmental assumptions and fairness conditions, and reaches a state that satisfies all the reachability conditions; that is, if the following LTL formula is satisfiable (in the chosen background theory):

   _I<sub>S</sub> ∧ **always** T<sub>S</sub> ∧ **always** A ∧ **always eventually** F ∧ **eventually** R_

 2. every property _P<sub>j</sub>_ is invariant for _S_ under the environmental assumptions and the fairness conditions; that is, if the following LTL formula is valid (in the chosen background theory):

    _I<sub>S</sub> ∧ **always** T<sub>S</sub> ∧ **always** A ∧ **always eventually** F ⇒ **always** P_


<!-- Each conjecture _C<sub>j</sub>_ is a _possible_ auxiliary invariant of _S_, that is, _(I<sub>S</sub> ∧ **always** T<sub>S</sub>) ∧ **always** (A<sub>1</sub> ∧ ⋅⋅⋅ ∧ A<sub>n</sub>) ⇒ **always** C<sub>i</sub>)_ is possibly valid. If it is indeed invariant, it may be used to help prove the properties _P_ invariant. -->



#### Examples

```scheme
;---------
; Arbiter
;---------

(define-system NonDetArbiter
  :input ( (req1 Bool) (req2 Bool) )
  :output ( (gran1 Bool) (gran2 Bool) )
  :local ( (s Bool) )
  :init ( (not gran1) (not gran2) )  ; nothing is granted initially
  :trans (
    (=> (and (not req1') (not req2'))
        (and (not gran1') (not gran2')))
    (=> (and req1' (not req2'))
        (and 'gran1 (not gran2')))
    (=> (and (not req1') req2')
        (and (not gran1') gran2'))
    (=> (and req1' req2')
        ; the unconstrained value of `s` is used as non-deterministic choice
        (ite s'
          (and gran1' (not gran2')
          (and (not gran1') gran2'))))
  ) 
)

(verify-system NonDetArbiter
  :input ( (r1 Bool) (r2 Bool) )
  :output ( (g1 Bool) (g2 Bool) )
  :properties (
    (p1 "Every request is immediately granted" ; not invariant
      (and (=> r1 g1) (=> r2 g2))
    )
    (p2 "In the absence of other requests, every request is immediately granted" ; invariant
      (=> (distinct r1 r2) 
          (and (=> r1 g1) (=> r2 g2)))
    )
    (p3 "A request is granted only if present" ; invariant
      (and (=> g1 r1) (=> g2 r2))
    )
    (p4 "At most one request is granted at any one time" ; invariant
      (not (and g1 g2)) 
    )
    (p5 "In case of concurrent requests one of them is always granted" ; invariant
      (=> (and r1 r2) (or g1 g2)) 
    )
    (p6 "If there have been no requests so far then there have been no grants" ; invariant
      (=> (historically (and (not r1) (not r2)))
          (historically (and (not g1) (not g2))))
    )
  ) 
)

(verify-system NonDetArbiter
  :input ( (r1 Bool) (r2 Bool) )
  :output ( (g1 Bool) (g2 Bool) )
  :assumptions (
    (a1 "There are no concurrent requests"
      (not (and r1 r2))
    )
  )
  :properties (
    (p1 "Every request is immediately granted" ; invariant
      (and (=> r1 g1) (=> r2 g2))
    )
  ) 
)

;---------------
; 3-bit counter
;---------------

(define-fun toBit ((b Bool)) Int (ite b 1 0))

(define-fun toInt ( (b2 Bool) (b1 Bool) (b0 Bool) ) Bool
  (+ (* 4 (toBit b2)) (* 2 (toBit b1)) (toBit b0))
)

(verify-system ThreeBitCounter
  :input ( (inc Bool) (start Bool) )
  :output ( (o0 Bool) (o1 Bool) (o2 Bool) )
  :local ( (c0 Bool) (c1 Bool) (c2 Bool) )
  :properties (
    (p1 "Sanity-check invariant" 
      (<= 0 (toInt o2 o1 o0) 7)
    )
    (p2 "A start signal resets the counter to 0 in the next" 
      (=> (before start) 
          (= 0 (toInt o2 o1 o0)))
    )
    (p2A "Alternative formulation of p2 as a transition invariant"
      (=> start 
          (= 0 (toInt o2' o1' o0')))
    )
    (p3 "If no increment requests are ever sent, the counter stays at 0"
      (=> (historically (not inc)) 
          (= (toInt o2 o1 o0) 0))
    )
    (p4 "If there is an increment request and the counter is below 7 
         then it will increase by 1 next"
      (let ( (n (toInt o2 o1 o0)) )
        (=> (and inc (< n 7)) 
            (= (toInt o2' o1' o0') (+ n 1))))
    )
  )
)

(define-system DelayedCounter
  :input ( (inc Bool) (start Bool) )
  :output ( (n Int) )
  :local ( (c Int) )
  :init ( 
    (= n 0) 
    (= c (ite (and inc (not start)) 1 0)) 
  )
  :trans ( 
    (= n' c) 
    (= c' (ite start' 0
            (ite (not inc') c 
              (ite (= c 7) 0 (+ c 1)))))
  )
)

(define-system CountObserver
  :input ( (inc Bool) (start Bool) )
  :output ( (n1 Int) (n2 Int) )
  :local ( (o0 Bool) (o1 Bool) (o2 Bool) )
  :init ( 
    (= n1 (count o2 o1 o0))
    (ThreeBitCounter inc start o0 o1 o2)
    (DelayedCounter inc start n2)
  )
  :trans ( 
    (= n1' (count o2' o1' o0'))
    (ThreeBitCounter inc start o0 o1 o2)
    (DelayedCounter inc start n2)
  )
)

; more concisely
(define-system CountObserver
  :input ( (inc Bool) (start Bool) )
  :output ( (n1 Int) (n2 Int) )
  :local ( (o0 Bool) (o1 Bool) (o2 Bool) )
  :inv ( (= n1 (count o2 o1 o0)) )
  :compose (
    (ThreeBitCounter inc start o0 o1 o2)
    (DelayedCounter inc start n2)
  )
)

(verify-system CountObserver
  :input ( (inc Bool) (start Bool) )
  :output ( (n1 Int) (n2 Int) )
  :properties (
    (p1 "" (= n1 n2))                                 ; not invariant
    (p2 "" (since start (= n1 n2)))                   ; not invariant
    (p3 "" (=> (once start) (since start (= n1 n2)))) ; invariant
  )
)
```

## Extensions

### Contracts

[more]

#### Examples

##### Thermostat Controller

```scheme
;            +-----------------------------------+
;            |  ThermostatController             |
;            |                                   |
;            |    +--------------------+         |
; --up----------->|                    |         |
;            |    |   SetDesiredTemp   |--+----------set_temp-->
; --down--------->|                    |  |      |
;            |    +--------------------+  |      |
;            |                            v      |
;            |    +--------------------------+   |
; -switch-------->|                          |-------cool-->
;            |    |       ControlTemp        |   |
; -out_temp------>|                          |-------heat-->
;            |    +--------------------------+   |
;            |                                   |
;            +-----------------------------------+

;-------------------
; Global parameters
;-------------------
;
(define-const MIN_TEMP Real 40.0)
(define-const MAX_TEMP Real 100.0)
(define-const INI_TEMP Real 70.0)
(define-const DEADBAND Real 3.0)
(define-const DIFF Real 3.0)

(declare-enum-sort SwitchPos (Cool Off Heat))

;----------------
; SetDesiredTemp
;----------------
;
(define-system SetDesiredTemp
  :input ( (up_button Bool) (down_button Bool) )
  :output ( (set_temp Real) )
  :auxiliary (
    (inc Bool 
      :def (and up_button (<= set_temp (- MAX_TEMP DIFF))))
    (dec Bool 
      :def (and down_button (>= set_temp (+ MIN_TEMP DIFF))))
  )
  :assumptions (
    (a1 "Up/Down button signals are mutually exclusive"
      (not (and up_button down_button))
    )
  )
  :guarantees (
    (g0 "Initial set_temp"
      (initially (= set_temp INIT_TEMP))
    )
    (g1 "set_temp increment"
      (=> inc (= set_temp' (+ set_temp DIFF)))
    )
    (g2 "set_temp decrement"
      (=> dec (= set_temp' (- set_temp DIFF)))
    )
    (g3 "set_temp invariance"
      (=> (not (or inc dec))
        (= set_temp' set_temp))
    )
  )
)

;-------------
; ControlTemp
;-------------
;
(define-system ControlTemp
  :input ( (switch SwitchPos) (current_temp Real) (set_temp Real) )
  :output ( (cool_act_sig Bool) (heat_act_sig Bool) )
  :auxiliary (
    (cool_start Bool
      :def (and (= switch Cool)
             (> current_temp (+ set_temp DEADBAND)))
    )
    (cool_mode Bool
      :init cool_start
      :next (or cool_start'
              (and cool_mode
                (= switch' Cool)
                (> current_temp' set_temp')))
    )
    (heat_start Bool
      :def (and (= switch Heat)
             (< current_temp (- set_temp DEADBAND)))
    )
    (heat_mode Bool 
      :init heat_start
      :next (or heat_start'
              (and heat_mode
                (= switch' Heat)
                (< current_temp' set_temp')))
    )
    (off_mode Bool 
      :def (and (not cool_mode) (not heat_mode))
    )
  )
  :guarantees (
    (g1 "Cooling activation"
      (= cool_act_sig cool_mode)
    )
    (g2 "Heating activation" 
      (= heat_act_sig heat_mode)
    )
    (g3 "Heating and cooling mutually exclusive"
      (not (and heat_act_sig cool_act_sig))
    )
  )
)

;----------------------
; ThermostatController
;----------------------
;
(define-system ThermostatController
  :input ( (switch SwitchPo) (up Bool) (down Bool) (in_temp Real) )
  :output ( (cool Bool) (heat Bool) (set_tempReal) )
  :inv (
    (SetDesireTemp up down set_temp)
    (ControlTemp switch in_temp set_temp cool heat)
  )
  :assumptions (
    (a1 "Up/Down button signals are mutually exclusive" 
      (not (and up_button down_button))
    )  

  )
  :auxiliary (
    (in_deadzone Bool
      :def (<= (- set_temp DEADBAND) in_temp (+ set_temp DEADBAND))
    )
    (system_off Bool
      :def (and (not cool) (not heat))
    )

  )
  :guarantees (
    (g1 "Initial temperature is in range":
      (<= MIN_TEM INIT_TEMP MAX_TEMP)
    )  
    (g2 "Deadband and Diff are positive values"
      (and (> DEADBAND 0.0) (> DIFF 0.0))
    )
    (g3 "No activation signal is enabled if switch is in Off"
      (=> (= switch Off) (and (not cool) (not heat)))
    )
    (g4 "Cooling system is turned On only if switch is in Cool"
      (=> cool (= switch Cool))
    )
    (g5 "Heating system is turned On only if switch is in Heat"
      (=> cool (= switch Heat))
    )
    (g6 "Activation signals are never enabled at the same time"
      (not (and cool heat))
    )
    (g7 "set_temp is always in range"
      (<= MIN_TEMP set_temp MAX_TEMP)
    )
    (g8 "set_temp doesn't change if no button is pressed"
      (=> (and (not up') (not down') 
        (= set_temp' set_temp))
    )      
    (g9 "set_temp doesn't decrease if the up button is pressed"
      (=> up' 
        (>= set_temp' set_temp))
    )
    (g10 "set_temp doesn't increase if the down button is pressed":
      (=> down' 
        (<= set_temp' set_temp))
    )
    (g11 "System is Off if indoor temperature is in the dead zone and system was Off in the previous step"
      (=> (and in_deadzone' system_off) system_off')
    )
    (g12 "Cooling system is On only if indoor temperature is higher than set_temp":
      (=> cool (> in_temp set_temp))
    )
    (g13 "Heating system is On only if indoor temperature is lower than set_temp":
      (=> heat (< in_temp set_temp))
    )
    (g14 "Cooling system is On if switch is in Cool and the indoor temperature is higher than set_temp plus deadband"
      (=> (and (= switch Cool) (> in_temp (+ set_temp DEADBAND)))
        cool)
    )
    (g15 "Heating system is On if switch is in Heat and the indoor temperature is lower than set_temp plus deadband"
      (=> (and (= switch Heat) (> in_temp (+ set_temp DEADBAND)))
        cool)
    )
    (g16 "Once cooling system is On, it remains On as long as set_temp has not been reached and switch is in Cool"
      (=> (and (since cool (= switch Cool))
            (> in_temp set_temp)) 
        cool))
    )
    (g17 "Once heating system is On, it remains On as long as set_temp has not been reached and switch is in Heat"
      (=> (and (since heat (= switch Heat))
            (< in_temp set_temp)) 
        heat))
    )
  )
)
```

## Parameters

[parameters as rigid variables]
