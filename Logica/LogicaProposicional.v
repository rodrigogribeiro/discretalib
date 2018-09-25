(** Tactic library for propositional logic natural deduction *)

(** identity *)

Ltac id H := exact H.

(** Implication *)

Ltac intro_implicacao :=
  match goal with
  | [ |-  _ -> _] => let Hx := fresh "H"
                  in intro Hx
  | [ |- _ ] => fail "A conclusão não é uma implicação"          
  end.

Ltac elim_implicacao IMP LHS :=
  match type of IMP with
  | ?T -> ?R =>
    match type of LHS with
    | ?T   => let Hx := fresh "H"
             in assert (Hx : R) by (apply IMP ; exact LHS)
    | _    => fail "O lado esquerdo da implicação não é igual ao segundo parâmetro"
    end
  | _      => fail "O primeiro parâmetro não é uma implicação"
  end.


(** conjunction *)

Ltac intro_e :=
  match goal with
  | [ |- _ /\ _ ] => split
  | [ |- _ ] => fail "A conclusão não é uma conjunção"
  end.

Ltac elim_e H :=
  match type of H with
  | ?A /\ ?B => let Hx := fresh "H"
            in assert (Hx : A /\ B) by auto ; destruct Hx
  | _     => fail "O parâmetro não é uma conjunção"
  end.


(** disjunction *)

Ltac intro_ou_esq :=
  match goal with
  | [ |- _ \/ _ ] => left
  | [ |- _ ] => fail "A conclusão não é uma disjunção"
  end.

Ltac intro_ou_dir := 
  match goal with
  | [ |- _ \/ _ ] => right
  | [ |- _ ] => fail "A conclusão não é uma disjunção"
  end.

Ltac elim_ou H :=
  match type of H with
  | ?A \/ ?B => let Hx := fresh "H"
              in assert (Hx : A \/ B) by auto ; destruct Hx
  | _     => fail "O parâmetro não é uma disjunção"
  end.

(** biconditional *)

Ltac intro_bicondicional :=
  match goal with
  | [ |- _ <-> _ ] => split
  | [ |- _ ] => fail "A conclusão não é um bicondicional"
  end.

Ltac elim_bicondicional H :=
  match type of H with
  | ?A <-> ?B => let Hx := fresh "H"
              in assert (Hx : A <-> B) by auto ; destruct Hx
  | _       => fail "O parâmetro não é um bicondicional"
  end.


(** negação *)

Ltac intro_negacao :=
  match goal with
  | [ |- ~ _ ] => intro
  | _         => fail "A conclusão não é uma negação"
  end.

Ltac elim_negacao NEG POS :=
  match type of NEG with
  | ~ ?A =>
    match type of POS with
    | ?A => let Hx := fresh "H"
           in assert (Hx : ~ A) by auto ; unfold not in Hx ; specialize (Hx POS)
    | _  => fail 2 "Os parâmetros fornecidos não permitem
                   aplicar a regra de eliminação da negação"
    end
  | _    => fail "O primeiro parâmetro não é uma negação"
  end.

(** contradição *)

Ltac contradicao H := apply False_ind with (P := H).

(** reduction ad absurdum *)

Axiom RAA : forall (P : Prop), ~~ P -> P. 

Ltac raa :=
  match goal with
  | [ |- ?A ] => let Hx := fresh "H"
               in apply RAA ; intro Hx
  end.