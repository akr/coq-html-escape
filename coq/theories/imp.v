From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Require Import htmlescape.listutils.
Require Import htmlescape.assoc.
Require Import htmlescape.ssrstr.

Definition assoc {A : eqType} {B : Type} (a : A) (al : seq (A * B)) :=
  nosimpl (@assoc.assoc A B a al).

Definition rassoc {A : Type} {B : eqType} (b : B) (al : seq (A * B)) :=
  nosimpl (@assoc.rassoc A B b al).

Definition html_escape_alist :=
  map (fun p => (p.1, seq_of_str p.2)) [::
  ("&"%char, "amp");
  ("<"%char, "lt");
  (">"%char, "gt");
  (""""%char, "quot");
  ("'"%char, "#39")
].

Definition html_escape_byte c :=
  if assoc c html_escape_alist is Some p then
    "&" ++ p.2 ++ ";"
  else
    [:: c].

Definition html_escape s := flatten (map html_escape_byte s).

Goal html_escape "abc&def<>""'" = "abc&amp;def&lt;&gt;&quot;&#39;". by []. Qed.

Definition html_char_entities :=
  map (fun p => (p.1, seq_of_str p.2)) [::
  ("&"%char, "amp");
  ("<"%char, "lt");
  (">"%char, "gt");
  (""""%char, "quot");
  ("'"%char, "apos")
  (* ... more character entities here ... *)
].

Fixpoint html_unescape s :=
  match s with
  | nil => nil
  | "&"%char :: s1 =>
      if ci_start_with "#x" s1 is Some n1 then
        let s2 := drop n1 s1 in
        let (v, n2) := decode_hex_prefix s2 in
        if n2 == 0 then "&"%char :: html_unescape s1 else
        let s3 := drop n2 s2 in
        if start_with ";" s3 is Some n3 then
          (ascii_of_nat v) :: html_unescape (drop n3 s3)
        else
          "&"%char :: html_unescape s1
      else if start_with "#" s1 is Some n1 then
        let s2 := drop n1 s1 in
        let (v, n2) := decode_decimal_prefix s2 in
        if n2 == 0 then "&"%char :: html_unescape s1 else
        let s3 := drop n2 s2 in
        if start_with ";" s3 is Some n3 then
          (ascii_of_nat v) :: html_unescape (drop n3 s3)
        else
          "&"%char :: html_unescape s1
      else if sindex ";"%char s1 is Some n1 then
        let name := take n1 s1 in
        let s2 := drop n1 s1 in
        if start_with ";" s2 is Some n2 then
          let s3 := drop n2 s2 in
          if rassoc name html_char_entities is Some (c, _) then
            c :: html_unescape s3
          else
            "&"%char :: html_unescape s1
        else
          "&"%char :: html_unescape s1
      else
        "&"%char :: html_unescape s1
  | c :: s1 => c :: html_unescape s1
  end.

(* pointer to byte (unsigned char).
  "cptr i lst" represents a pointer to i'th char in lst.
  restriction: 0 <= i <= size lst.
  Although a pointer with i = size lst is valid, its dereference is invalid.
*)
Inductive byteptr := bptr : nat -> seq ascii -> byteptr.

(* accessors for Coq proof *)
Definition i_of_bptr ptr := let: bptr i s := ptr in i.
Definition s_of_bptr ptr := let: bptr i s := ptr in s.

(* precondition: i + n <= size s
  C: p + n *)
Definition bptradd ptr n :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  bptr (i + n) s.

(* precondition: n <= i
  C: p - n *)
Definition bptrsub ptr n :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  bptr (i - n) s.

(* precondition: i < size s
  C: *p *)
Definition bptrget ptr :=
  let i := i_of_bptr ptr in
  let s := s_of_bptr ptr in
  nth "000"%char s i.

(* buffer implemented using Ruby String.
  Encoding is not considiered.
  The C type is struct rbuf { size_t len; VALUE str }.
  "len" is used to detect the non-linear use of the string.
  If the string is used linearly, len == RSTRING_LEN(str) is hold.
  We assume this condition in following explanation.
 *)
Inductive buffer := bufctr of seq ascii.

(* accessor for Coq proof *)
Definition s_of_buf buf := let: bufctr s := buf in s.

(* (struct rbuf){ len + 1, rb_str_buf_cat(str, &b, 1) } *)
Definition bufaddbyte buf b :=
  let s := s_of_buf buf in
  bufctr (rcons s b).

(* precondition: i + n <= size s'
  (struct rbuf){ len + n, rb_str_buf_cat(str, ptr, n) }
 *)
Definition bufaddmem buf ptr n :=
  let s := s_of_buf buf in
  let i := i_of_bptr ptr in
  let s' := s_of_bptr ptr in
  bufctr (s ++ take n (drop i s')).

(* This function will be implemented as a table in C *)
Definition html_escape_byte_table c :=
  if assoc c html_escape_alist is Some p then
    let s := "&" ++ p.2 ++ ";" in
    (bptr 0 s, size s)
  else
    (bptr 0 [:: c], 1).

Fixpoint trec_html_escape buf ptr n :=
  match n with
  | 0 => buf
  | n'.+1 =>
      let: (escptr, escn) := html_escape_byte_table (bptrget ptr) in
      trec_html_escape
        (bufaddmem buf escptr escn)
        (bptradd ptr 1)
        n'
  end.

Definition trec_html_escape_stub s :=
  s_of_buf (trec_html_escape (bufctr [::]) (bptr 0 s) (size s)).

Inductive m128 := c128 :
  ascii -> ascii -> ascii -> ascii ->
  ascii -> ascii -> ascii -> ascii ->
  ascii -> ascii -> ascii -> ascii ->
  ascii -> ascii -> ascii -> ascii -> m128.

Definition seq_of_m128 m :=
  let: c128 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf := m in
  [:: b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; ba; bb; bc; bd; be; bf].

Definition m128_of_seq s := c128
  (nth "000"%char s 0) (nth "000"%char s 1) (nth "000"%char s 2) (nth "000"%char s 3)
  (nth "000"%char s 4) (nth "000"%char s 5) (nth "000"%char s 6) (nth "000"%char s 7)
  (nth "000"%char s 8) (nth "000"%char s 9) (nth "000"%char s 10) (nth "000"%char s 11)
  (nth "000"%char s 12) (nth "000"%char s 13) (nth "000"%char s 14) (nth "000"%char s 15).

Definition m128_of_bptr ptr := m128_of_seq (drop (i_of_bptr ptr) (s_of_bptr ptr)).

(* _mm_cmpestri(a, la, b, lb,
     _SIDD_UBYTE_OPS|_SIDD_CMP_EQUAL_ANY|
     _SIDD_POSITIVE_POLARITY|_SIDD_LEAST_SIGNIFICANT) *)
Definition cmpestri_ubyte_eqany_ppol_lsig (a : m128) (la : nat) (b : m128) (lb : nat) :=
  let sa := take la (seq_of_m128 a) in
  let sb := take lb (seq_of_m128 b) in
  let p := mem sa in
  if has p sb then find p sb else 16.

Definition chars_to_escape_list := [:: "&"%char; "<"%char; ">"%char; """"%char; "'"%char].
Definition chars_to_escape := m128_of_seq chars_to_escape_list.
Definition num_chars_to_escape := size chars_to_escape_list.

Fixpoint sse_html_escape buf ptr m n :=
  match n with
  | 0 => bufaddmem buf ptr m
  | n'.+1 =>
      let p1 := bptradd ptr m in
      if n <= 15 then
        trec_html_escape (bufaddmem buf ptr m) p1 n
      else
        let i := cmpestri_ubyte_eqany_ppol_lsig
            chars_to_escape num_chars_to_escape
            (m128_of_bptr p1) 16 in
        if 16 <= i then
          sse_html_escape buf ptr (m + 16) (n' - 15)
        else
          let buf2 := bufaddmem buf ptr (m + i) in
          let p2 := bptradd ptr (m + i) in
          let c := bptrget p2 in
          let p3 := bptradd p2 1 in
          let: (escptr, escn) := html_escape_byte_table c in
          let buf3 := bufaddmem buf2 escptr escn in
          sse_html_escape buf3 p3 0 (n' - i)
  end.

Definition sse_html_escape_stub s :=
  s_of_buf (sse_html_escape (bufctr [::]) (bptr 0 s) 0 (size s)).
