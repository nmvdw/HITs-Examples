Require Import HoTT HitTactics.
Require Export Mod2.

From HoTTClasses Require Import interfaces.abstract_algebra tactics.ring_tac.

Section Mod2_ring.

Instance Mod2_plus : Plus Mod2 := Mod2.plus.
Instance Mod2_mult : Mult Mod2 := Mod2.mult.
Instance Mod2_zero : Zero Mod2 := Z.
Instance Mod2_one  : One  Mod2 := succ Z.

End Mod2_ring.
