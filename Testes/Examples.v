Require Import discretalib.Logica.LogicadePredicados.

(** Examples of the library *)

Section PROPLOGIC.
  Variables A B C : Prop.

  Lemma teste1 : (A -> B) -> A -> B.
  Proof.
    intro_implicacao.
    intro_implicacao.
    elim_implicacao H H0.
    id H1.
  Qed.
  
  Lemma teste2 (H : A /\ B) : B /\ A.
  Proof.
    intro_e.
    +
      elim_e H.
      id H1.
    +
      elim_e H.
      id H0.
  Qed.

  Lemma teste3 : A \/ B -> (A -> C) -> (B -> C) -> C.
  Proof.
    intro_implicacao.
    intro_implicacao.
    intro_implicacao.
    elim_ou H.
    +
      elim_implicacao H0 H2.
      id H3.
    +
      elim_implicacao H1 H2.
      id H3.
  Qed.

  Lemma teste4 : A <-> B -> B <-> A.
  Proof.
    intro_implicacao.
    elim_bicondicional H.
    intro_bicondicional.
    +
      id H1.
    +
      id H0.
  Qed.
  
  Lemma teste5 : ~ A -> A -> False.
  Proof.
    intro_implicacao.
    intro_implicacao.
    elim_negacao H H0.
    id H1.
  Qed.
  
  Lemma teste6 : ~ A -> A -> False.
  Proof.
    intro_implicacao.
    intro_implicacao.
    contradicao False.
    elim_negacao H H0.
    id H1.
  Qed.

  Lemma teste7 : (A \/ B) -> ~ A -> B.
  Proof.
    intro_implicacao.
    intro_implicacao.
    elim_ou H.
    +
      contradicao B.
      elim_negacao H0 H.
      id H2.
    +
      id H1.
  Qed.
  
  Lemma teste8 : (A -> B) -> (~ A \/ B).
  Proof.
    intro_implicacao.
    raa.
    assert (Ha : (~ A \/ B)).
    +
      intro_ou_esq.
      intro_negacao.
      assert(Ha1 : ~ A \/ B).
      *
        intro_ou_dir.
        elim_implicacao H H1.
        id H2.
      *
        elim_negacao H0 Ha1.
        id H2.
    +
      elim_negacao H0 Ha.
      id H1.
  Qed.
  
End PROPLOGIC.

Section PREDLOGIC.
  Variable A : Set.
  Variables P Q : A -> Prop.

  Lemma ex1 (H : forall x : A, P x -> Q x) : (forall x, ~ Q x) -> (forall x, ~ P x).
  Proof.
    intro_implicacao.
    intro_para_todo.
    intro_negacao.
    dup H.
    elim_para_todo H x.
    elim_implicacao H H1.
    elim_para_todo H0 x.
    elim_negacao H0 H4.
    id H6.
  Qed.

  Lemma ex2 (H : exists x : A, ~ P x) : ~ forall x : A, P x.
  Proof.
    intro_negacao.
    elim_existe H.
    elim_para_todo H0 x.
    elim_negacao Hx H0.
    id H1.
  Qed.
End PREDLOGIC.