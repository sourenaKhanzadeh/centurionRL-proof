Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday | sunday.


Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => sunday
  | sunday => monday
  end.

Example test_next_weekday :
  (next_weekday (next_weekday monday)) = wednesday.

Proof.
  simpl.
  reflexivity.
Qed.



