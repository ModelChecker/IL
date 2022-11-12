


Let _I<sub>S</sub>_ and _T<sub>S</sub>_ be respectively the initial state condition and transition predicate of $S$.

Let _A = A<sub>1</sub> \land \cdots \land A<sub>q</sub>_, _F = F<sub>1</sub> \land \cdots \land F<sub>h</sub>_, _R = R<sub>1</sub> \land \cdots \land R<sub>i</sub>_, _P = P<sub>1</sub> \land \cdots \land P<sub>k</sub>_.

The command above succeeds if both the following holds:

1. there is a trace of $S$ that satisfies all the environmental assumptions and fairness conditions, and reaches a state that satisfies all the reachability conditions; that is, if the following LTL formula is satisfiable (in the chosen background theory):

   _I<sub>S</sub> ∧ **always** T<sub>S</sub> ∧ **always** A ∧ **always eventually** F ∧ **eventually** R_

 2. every property _P<sub>j</sub>_ is invariant for $S$ under the environmental assumptions and the fairness conditions; that is, if the following LTL formula is valid (in the chosen background theory):

    _I<sub>S</sub> ∧ **always** T<sub>S</sub> ∧ **always** A ∧ **always eventually** F ⇒ **always** P_


<!-- Each conjecture _C<sub>j</sub>_ is a _possible_ auxiliary invariant of $S$, that is, _(I<sub>S</sub> ∧ **always** T<sub>S</sub>) ∧ **always** (A<sub>1</sub> \land \cdots \land A<sub>n</sub>) ⇒ **always** C<sub>i</sub>)_ is possibly valid. If it is indeed invariant, it may be used to help prove the properties _P_ invariant. -->



#### Examples

```scheme
;---------
; Arbiter
;---------

(define-system NonDetArbiter
  :input ( (r1 Bool) (r2 Bool) )
  :output ( (g1 Bool) (g2 Bool) )
  :local ( (s Bool) )
  :init ( (not g1) (not g2) )  ; nothing is granted initially
  :trans (
    (=> (and (not r1') (not r2'))
        (and (not g1') (not g2')))
    (=> (and r1' (not r2'))
        (and 'g1 (not g2')))
    (=> (and (not r1') r2')
        (and (not g1') g2'))
    (=> (and r1' r2')
        ; the unconstrained value of `s` is used as non-deterministic choice
        (ite s'
          (and g1' (not g2')
          (and (not g1') g2'))))
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

-->