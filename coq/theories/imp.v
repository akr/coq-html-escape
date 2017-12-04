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
  "bptr addr i lst" represents a pointer to i'th char in lst.
  addr is the machine address of the first element.
  addr is used only for alignment calclation.
  restriction: 0 <= i <= size lst.
  Although a pointer with i = size lst is valid, its dereference is invalid.
*)
Inductive byteptr := bptr : nat -> nat -> seq ascii -> byteptr.

(* accessors for Coq proof *)
Definition i_of_bptr ptr := let: bptr addr i s := ptr in i.
Definition s_of_bptr ptr := let: bptr addr i s := ptr in s.
Definition addr_of_bptr ptr := let: bptr addr i s := ptr in addr.
Definition align_of_bptr n ptr := (addr_of_bptr ptr) %% n.

Lemma let_bptr_destruct T (B : nat -> nat -> seq ascii -> T) ptr :
  (let: bptr addr i s := ptr in B addr i s) =
  B (addr_of_bptr ptr) (i_of_bptr ptr) (s_of_bptr ptr).
Proof. by case: ptr. Qed.

(* precondition: i + n <= size s
  C: p + n *)
Definition bptradd ptr n :=
  let: bptr addr i s := ptr in
  bptr addr (i + n) s.

(* precondition: n <= i
  C: p - n *)
Definition bptrsub ptr n :=
  let: bptr addr i s := ptr in
  bptr addr (i - n) s.

(* precondition: i < size s
  C: *p *)
Definition bptrget ptr :=
  let: bptr addr i s := ptr in
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

Lemma let_buffer_destruct T (B : seq ascii -> T) buf :
  (let: bufctr s := buf in B s) =
  B (s_of_buf buf).
Proof. by case: buf. Qed.

(* (struct rbuf){ len + 1, rb_str_buf_cat(str, &b, 1) } *)
Definition bufaddbyte buf b :=
  let: bufctr s := buf in
  bufctr (rcons s b).

(* precondition: i + n <= size s'
  (struct rbuf){ len + n, rb_str_buf_cat(str, ptr, n) }
 *)
Definition bufaddmem buf ptr n :=
  let: bufctr s := buf in
  let: bptr addr i s' := ptr in
  bufctr (s ++ take n (drop i s')).

(* This function will be implemented as a table in C *)
(* The addresses of strings are 0 which means they are aligned for all purpose. *)
Definition html_escape_byte_table c :=
  if assoc c html_escape_alist is Some p then
    let s := "&" ++ p.2 ++ ";" in
    (bptr 0 0 s, size s)
  else
    (bptr 0 0 [:: c], 1).

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

Definition trec_html_escape_stub addr s :=
  s_of_buf (trec_html_escape (bufctr [::]) (bptr addr 0 s) (size s)).

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

Definition sse_html_escape_stub addr s :=
  s_of_buf (sse_html_escape (bufctr [::]) (bptr addr 0 s) 0 (size s)).

(* convert first 8 bit *)
Definition ascii_of_bits s :=
  Ascii (nth false s 0) (nth false s 1) (nth false s 2) (nth false s 3)
        (nth false s 4) (nth false s 5) (nth false s 6) (nth false s 7).

Definition bits_of_ascii c :=
  let: Ascii b0 b1 b2 b3 b4 b5 b6 b7 := c in
  [:: b0; b1; b2; b3; b4; b5; b6; b7].

(*
Lemma ascii_of_bits_of_ascii c : ascii_of_bits (bits_of_ascii c) = c.
Proof. by case: c. Qed.

Lemma bits_of_ascii_of_bits s := *)

Definition m128_of_bits s :=
  m128_of_seq (map ascii_of_bits (reshape (nseq 16 8) s)).

Definition bits_of_m128 m :=
  flatten (map bits_of_ascii (seq_of_m128 m)).

(* _mm_cmpestrm(a, la, b, lb,
     _SIDD_UBYTE_OPS|_SIDD_CMP_EQUAL_ANY|
     _SIDD_POSITIVE_POLARITY|_SIDD_LEAST_SIGNIFICANT|_SIDD_BIT_MASK) *)
Definition cmpestrm_ubyte_eqany_ppol_lsig_bitmask
  (a : m128) (la : nat) (b : m128) (lb : nat) : m128 :=
  let sa := take la (seq_of_m128 a) in
  let sb := take lb (seq_of_m128 b) in
  let p := mem sa in
  let bits := map p sb in
  m128_of_bits bits.

(* _mm_cmpestrc(a, la, b, lb,
     _SIDD_UBYTE_OPS|_SIDD_CMP_EQUAL_ANY|
     _SIDD_POSITIVE_POLARITY|_SIDD_LEAST_SIGNIFICANT|_SIDD_BIT_MASK) *)
Definition cmpestrc_ubyte_eqany_ppol_lsig_bitmask
  (a : m128) (la : nat) (b : m128) (lb : nat) : bool :=
  let sa := take la (seq_of_m128 a) in
  let sb := take lb (seq_of_m128 b) in
  let p := mem sa in
  has p sb.

Fixpoint nat_of_bits (s : seq bool) :=
  match s with
  | [::] => 0
  | b :: s' => b + 2 * (nat_of_bits s')
  end.

Fixpoint lobits_of_nat m n :=
  match m with
  | 0 => [::]
  | m'.+1 => (odd n) :: (lobits_of_nat m' n./2)
  end.

(* _mm_cvtsi128_si64(a) *)
Definition lo64_of_m128 (a : m128) : nat :=
  nat_of_bits (take 64 (bits_of_m128 a)).

(* _mm_cvtsi128_si64(a) & 0xff *)
Definition m128_firstbyte m :=
  let: c128 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf := m in
  b0.

(* _mm_bsrli_si128(a, 1) *)
Definition m128_restbytes m :=
  let: c128 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf := m in
  c128 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf "000"%char.

Definition popcount64 (n : nat) :=
  count_mem true (lobits_of_nat 64 n).

Fixpoint sse_html_escape2_dense buf ptr m i mask bytes :=
  match i with
  | 0 => (buf, ptr, m)
  | i'.+1 =>
    if odd mask then
      let buf1 := if m is 0 then buf else bufaddmem buf ptr m in
      let c := m128_firstbyte bytes in
      let rest := m128_restbytes bytes in
      let: (escptr, escn) := html_escape_byte_table c in
      let buf2 := bufaddmem buf1 escptr escn in
      let ptr2 := bptradd ptr m.+1 in
      sse_html_escape2_dense buf2 ptr2 0 i' mask./2 rest
    else
      let rest := m128_restbytes bytes in
      sse_html_escape2_dense buf ptr m.+1 i' mask./2 rest
  end.

Fixpoint sse_html_escape2_aligned buf ptr m nn {struct nn} :=
  match nn with
  | 0 => (buf, ptr, m)
  | nn'.+1 =>
      let p1 := bptradd ptr m in
      let bytes16 := m128_of_bptr p1 in
      let c := cmpestrc_ubyte_eqany_ppol_lsig_bitmask chars_to_escape num_chars_to_escape bytes16 16 in
      let mask' := cmpestrm_ubyte_eqany_ppol_lsig_bitmask chars_to_escape num_chars_to_escape bytes16 16 in
      if c then
        let mask := (lo64_of_m128 mask') in
        let: (buf2, ptr2, m2) := sse_html_escape2_dense buf ptr m 16 mask bytes16 in
        sse_html_escape2_aligned buf2 ptr2 m2 nn'
      else
        sse_html_escape2_aligned buf ptr (m + 16) nn'
  end.

Definition sse_html_escape2 buf ptr n :=
  if n <= 15 then
    trec_html_escape buf ptr n
  else
    let left_align := align_of_bptr 16 ptr in
    let left_len := if left_align is 0 then 0 else 16 - left_align in
    let buf2 := trec_html_escape buf ptr left_len in
    let ptr2 := bptradd ptr left_len in
    let n2 := n - left_len in
    let mid_count := n2 %/ 16 in
    let right_len := n2 %% 16 in
    let: (buf3, ptr3, m3) := sse_html_escape2_aligned buf2 ptr2 0 mid_count in
    let buf4 := if m3 is 0 then buf3 else bufaddmem buf3 ptr3 m3 in
    let ptr4 := bptradd ptr (n2 - right_len) in
    trec_html_escape buf4 ptr4 right_len.

