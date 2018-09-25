(** Tactic library for predicate logic natural deduction *)

Require Export discretalib.Logica.LogicaProposicional.

Ltac dup H :=
  match type of H with
  | ?T => let H1 := fresh "H"
         in assert (H1 : T) by (exact H)
  end.

(** universal quantification *)

Ltac intro_para_todo :=
  match goal with
  | [ |- forall x, _] => intro
  | _ => fail "A conclusão não envolve um quantificador universal"
  end.

Inductive no_argument : Set := NoArg : no_argument.

Ltac elim_para_todo_aux H :=
  match type of H with
  | forall (_ : ?T), _ => let y := fresh "y" in
                    assert (y : T) by admit ;
                    dup H ;
                    specialize (H y)
  | _ => fail "A hipótese fornecida não envolve o quantificador universal"
  end.


Ltac elim_para_todo_real H x :=
  match type of x with
  | no_argument => elim_para_todo_aux H
  | _           =>
    match type of H with
    | forall ( _ : ?T), _  =>
      match type of x with
      | ?T => dup H ; specialize (H x)
      | _ => fail "O argumento não pertence ao universo de discurso da hipótese" 2
      end
    | _ => fail "A hipótese fornecida não envolve o quantificador universal"
    end
  end.

Tactic Notation "elim_para_todo" constr(H) := elim_para_todo_real H NoArg.
Tactic Notation "elim_para_todo" constr(H) constr(x) := elim_para_todo_real H x.

(** existential quantification *)

Ltac intro_existe v :=
  match goal with
  | [ |- exists _ , _ ] => exists v
  | _ => fail "A conclusão não envolve um quantificador existencial"
  end.

Ltac elim_existe H :=
  match type of H with
  | exists _ , _ => let x := fresh "x"
              in let Hx := fresh "Hx"
              in destruct H as [x Hx]
  | _ => fail "A hipótese fornecida não envolve o quantificador existencial"
  end.
