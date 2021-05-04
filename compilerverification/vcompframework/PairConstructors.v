Definition pair_fun0 {A B} (fA: A) (fB: B): A * B :=
  (fA, fB).

Definition pair_fun1 {A B} (fA: A -> A) (fB: B -> B): A * B -> A * B :=
  fun x => match x with (xa, xb) => (fA xa, fB xb) end.

Definition pair_fun2 {A B} (fA: A -> A -> A) (fB: B -> B -> B): A * B -> A * B -> A * B :=
  fun x y => match x, y with (xa, xb), (ya, yb) => (fA xa ya, fB xb yb) end.

Definition pair_binder {A B} (fA: (nat -> A) -> A) (fB: (nat -> B) -> B):
  (nat -> A * B) -> A * B :=
  fun xs => (fA (fun n => match xs n with (xa, xb) => xa end),
             fB (fun n => match xs n with (xa, xb) => xb end)).

Definition pair_rel1 {A B} (PA: A -> Prop) (PB: B -> Prop): A * B -> Prop :=
  fun x => match x with (xa, xb) => PA xa /\ PB xb end.

Definition pair_rel2 {A B} (PA: A -> A -> Prop) (PB: B -> B -> Prop): A * B -> A * B -> Prop :=
  fun x y => PA (fst x) (fst y) /\ PB (snd x) (snd y).

Definition pair_set_summary {A B} (fA: (A -> Prop) -> A) (fB: (B -> Prop) -> B):
  (A * B -> Prop) -> A * B :=
  fun xs => (fA (fun a => exists c, xs c /\ fst c = a),
             fB (fun b => exists c, xs c /\ snd c = b)).

