From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.

Definition html_char_entities :=
  map (fun p => (p.1, seq_of_str p.2)) [::
  ("&"%char, "amp");
  ("<"%char, "lt");
  (">"%char, "gt");
  (""""%char, "quot");
  ("'"%char, "apos")
  (* ... more character entities here ... *)
].

(* HTML character and text specification.
 * https://html.spec.whatwg.org/multipage/syntax.html#text-2
 * Note: Unicode is not considered.
 *)
Inductive char_spec : ascii -> seq ascii -> Prop :=
  | char_normal : forall c, c != "&"%char -> char_spec c [:: c]
  | char_named : forall c entity, (c, entity) \in html_char_entities ->
      char_spec c ("&" ++ entity ++ ";")
  | char_dec : forall m digs, digs != nil -> decode_decimal digs = Some m ->
      char_spec (ascii_of_nat m) ("&#" ++ digs ++ ";")
  | char_hex : forall x m xdigs,
      downcase_ascii x == "x"%char -> xdigs != nil -> decode_hex xdigs = Some m ->
      char_spec (ascii_of_nat m) ("&#" ++ x :: xdigs ++ ";").

Inductive text_spec : seq ascii -> seq ascii -> Prop :=
  | text_empty : text_spec [::] [::]
  | text_cons : forall c s raw escaped,
      char_spec c s -> text_spec raw escaped -> text_spec (c :: raw) (s ++ escaped).
