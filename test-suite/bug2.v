Require Import MetaCoq.Template.Loader.

Definition I (t:Type) (x:t) : t := x.
Definition II := I (forall t:Type, t -> t) I.
Quote Recursively Definition qII := II.
