Module Decidability.
Require Export form name.
Import Name Form.

Axiom name_dec : forall x y:Name, {x = y} + {x <> y}.
Axiom form_dec : forall x y:Formula, {x = y} + {x <> y}.
Axiom conf_dec : forall x y:Configuration, {x = y} + {x <> y}.

End Decidability.