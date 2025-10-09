import Mathlib.Tactic

/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers `ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the `OfNat` typeclass.
-/

namespace AppendixB

/- The ten digits, together with the base 10 -/
example : 0 = Nat.zero := rfl
example : 1 = (0:Nat).succ := rfl
example : 2 = (1:Nat).succ := rfl
example : 3 = (2:Nat).succ := rfl
example : 4 = (3:Nat).succ := rfl
example : 5 = (4:Nat).succ := rfl
example : 6 = (5:Nat).succ := rfl
example : 7 = (6:Nat).succ := rfl
example : 8 = (7:Nat).succ := rfl
example : 9 = (8:Nat).succ := rfl
example : 10 = (9:Nat).succ := rfl

/-- Definition B.1.1 -/
def Digit := Fin 10

instance Digit.instZero : Zero Digit := ⟨0, by decide⟩
instance Digit.instOne : One Digit := ⟨1, by decide⟩
instance Digit.instTwo : OfNat Digit 2 := ⟨2, by decide⟩
instance Digit.instThree : OfNat Digit 3 := ⟨3, by decide⟩
instance Digit.instFour : OfNat Digit 4 := ⟨4, by decide⟩
instance Digit.instFive : OfNat Digit 5 := ⟨5, by decide⟩
instance Digit.instSix : OfNat Digit 6 := ⟨6, by decide⟩
instance Digit.instSeven : OfNat Digit 7 := ⟨7, by decide⟩
instance Digit.instEight : OfNat Digit 8 := ⟨8, by decide⟩
instance Digit.instNine : OfNat Digit 9 := ⟨9, by decide⟩

instance Digit.instFintype : Fintype Digit := Fin.fintype 10
instance Digit.instDecidableEq : DecidableEq Digit := instDecidableEqFin 10

instance Digit.instInhabited : Inhabited Digit := ⟨ 0 ⟩

@[coe]
abbrev Digit.toNat (d:Digit) : ℕ := d.val

instance Digit.instCoeNat : Coe Digit Nat where
  coe := toNat

theorem Digit.lt (d:Digit) : (d:ℕ) < 10 := d.isLt

abbrev Digit.mk {n:ℕ} (h: n < 10) : Digit := ⟨n, h⟩

@[simp]
theorem Digit.toNat_mk {n:ℕ} (h: n < 10) : (Digit.mk h:ℕ) = n := rfl

@[simp]
theorem Digit.inj (d d':Digit) : d = d' ↔ (d:ℕ) = d' := by grind

theorem Digit.mk_eq_iff (d:Digit) {n:ℕ} (h: n < 10) : d = mk h ↔ (d:ℕ) = n := by
  convert Digit.inj d (mk h)
#check (0:Digit)
#check (1:Digit)
#check (2:Digit)
#check (3:Digit)
#check (4:Digit)
#check (5:Digit)
#check (6:Digit)
#check (7:Digit)
#check (8:Digit)
#check (9:Digit)

theorem Digit.eq (n: Digit) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  fin_cases n <;> simp

/-- Definition B.1.2 -/
structure PosintDecimal where
  digits : List Digit
  nonempty : digits ≠ []
  nonzero : digits.head nonempty ≠ 0

theorem PosintDecimal.congr' {p q:PosintDecimal} (h: p.digits = q.digits) : p = q := by
  obtain ⟨ pd, _, _ ⟩ := p
  obtain ⟨ qd, _, _ ⟩ := q
  congr

theorem PosintDecimal.congr {p q:PosintDecimal} (h: p.digits.length = q.digits.length)
  (h': ∀ (n:ℕ) (h₁ : n < p.digits.length) (h₂: n < q.digits.length), p.digits.get ⟨ n, h₁ ⟩ = q.digits.get ⟨ n, h₂ ⟩) : p = q := by
  apply congr'
  simp_all [List.ext_get_iff]

abbrev PosintDecimal.head (p:PosintDecimal): Digit := p.digits.head p.nonempty

theorem PosintDecimal.head_ne_zero (p:PosintDecimal) : p.head ≠ 0 := p.nonzero

theorem PosintDecimal.head_ne_zero' (p:PosintDecimal) : (p.head:ℕ) ≠ 0 := by
  by_contra!
  apply head_ne_zero p
  simp_all [Digit.toNat]

theorem PosintDecimal.length_pos (p:PosintDecimal) : 0 < p.digits.length := by
  simp [List.length_pos_iff, p.nonempty]

/-- A slightly clunky way of creating decimals. -/
def PosintDecimal.mk' (head:Digit) (tail:List Digit) (h: head ≠ 0) : PosintDecimal := {
  digits := head :: tail
  nonempty := by aesop
  nonzero := h
}

-- the positive integer decimal 314
#check PosintDecimal.mk' 3 [1, 4] (by decide)

-- the positive integer decimal 3
#check PosintDecimal.mk' 3 [] (by decide)

-- the positive integer decimal 10
#check PosintDecimal.mk' 1 [0] (by decide)

/-- We are indexing digits in a decimal from left to right rather than from right to left, thus necessitating a reversal here. -/
@[coe]
def PosintDecimal.toNat (p:PosintDecimal) : Nat :=
  ∑ i:Fin p.digits.length, p.digits[p.digits.length - 1 - ↑i].toNat * 10 ^ (i:ℕ)

instance PosintDecimal.instCoeNat : Coe PosintDecimal Nat where
  coe := toNat

example : (PosintDecimal.mk' 3 [1, 4] (by decide):ℕ) = 314 := by decide

/-- Remark B.1.3 -/
@[simp]
theorem PosintDecimal.ten_eq_ten : (mk' 1 [0] (by decide):ℕ) = 10 := by
  simp [toNat, mk', Digit.toNat]

theorem PosintDecimal.digit_eq {d:Digit} (h: d ≠ 0) : (mk' d [] h:ℕ) = d := by
  simp [toNat, mk']

theorem PosintDecimal.pos (p:PosintDecimal) : 0 < (p:ℕ) := by
  simp [toNat]
  calc
    _ < (p.head:ℕ) * 10 ^ (p.digits.length - 1) := by
      have := p.head_ne_zero'
      positivity
    _ ≤ _ := by
      have := p.length_pos
      set a : Fin p.digits.length := ⟨ p.digits.length - 1, by omega ⟩
      convert Finset.single_le_sum _ (Finset.mem_univ a)
      . simp [a, head, List.head_eq_getElem]
      . infer_instance
      grind

/-- An operation implicit in the proof of Theorem B.1.5: -/
abbrev PosintDecimal.append (p:PosintDecimal) (d:Digit) : PosintDecimal :=
  mk' p.head (p.digits.tail ++ [d]) p.head_ne_zero

@[simp]
theorem PosintDecimal.append_toNat (p:PosintDecimal) (d:Digit) :
  (p.append d:ℕ) = d.toNat + 10 * p.toNat  := by
  simp [append, toNat, mk', Finset.mul_sum]
  rw [Fin.sum_univ_succAbove _ 0]
  congr 1
  . simp
  have := p.length_pos
  convert Fin.sum_congr' _ _ with i; swap; grind
  simp
  trans p.digits[p.digits.length - 1 - (i:ℕ)].toNat * (10^(i:ℕ) * 10); swap; ring
  congr 2
  have : p.head :: (p.digits.tail ++ [d]) = p.digits ++ [d] := by
    rw [←List.cons_append, head, List.cons_head_tail]
  have hlen : p.digits.length - 1 - ↑i < (p.digits ++ [d]).length := by grind
  calc
    _ = (p.digits ++ [d])[p.digits.length - 1 - ↑i] := by congr
    _ = _ := List.getElem_append_left _

theorem PosintDecimal.eq_append {p:PosintDecimal} (h: 2 ≤ p.digits.length) : ∃ (q:PosintDecimal) (d:Digit), p = q.append d := by
  use mk' p.head (p.digits.tail.dropLast) p.head_ne_zero
  set a := p.digits.getLast p.nonempty; use a
  apply congr'
  simp [mk']
  rw [←p.digits.cons_head_tail p.nonempty]
  congr 1
  convert (List.dropLast_append_getLast _).symm using 2; grind
  simp [←List.length_pos_iff]; omega

/-- Theorem B.1.5 (Uniqueness and existence of decimal representations) -/
theorem PosintDecimal.exists_unique (n:ℕ) : n > 0 → ∃! p:PosintDecimal, (p:ℕ) = n := by
  -- this proof is written to follow the structure of the original text.
  apply n.case_strong_induction_on
  . simp
  -- note: the variable `m` in the text is referred to as `m+1` here.
  clear n; intro m hind _
  obtain hm | hm := lt_or_ge m 9
  . apply ExistsUnique.intro (mk' (.mk (show m+1 < 10 by omega)) [] (by simp [Digit.mk]))
    . simp [mk', Digit.mk, toNat, Digit.toNat]
    intro d hd
    obtain hdl | hdl := lt_or_ge d.digits.length 2
    . replace hdl : d.digits.length = 1 := by linarith [d.length_pos]
      have _subsing : Subsingleton (Fin d.digits.length) := by simp [Fin.subsingleton_iff_le_one, hdl]
      let zero : Fin d.digits.length := ⟨ 0, by omega ⟩
      simp [toNat, hdl, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at hd
      apply congr
      . simp [hdl, mk']
      intro i hi₁ hi₂
      replace hi₁ : i = 0 := by omega
      simp [hi₁, mk', Digit.mk, hd]
    have : d.toNat ≥ 10 := calc
      _ ≥ (d.head:ℕ) * 10^(d.digits.length-1) := by
        set a : Fin d.digits.length := ⟨ d.digits.length - 1, by omega ⟩
        convert Finset.single_le_sum _ (Finset.mem_univ a)
        . simp [a, head, List.head_eq_getElem]
        . infer_instance
        intros; positivity
      _ ≥ 1 * 10^(2-1) := by
        gcongr
        . have := d.head_ne_zero'; omega
        norm_num
      _ = 10 := by norm_num
    linarith
  have := (m+1).mod_add_div 10
  set s := (m+1)/10
  set r := (m+1) % 10
  have hr : r < 10 := by grind
  specialize hind s _ _ <;> try linarith
  choose b hb huniq using hind; simp at huniq
  apply ExistsUnique.intro (b.append (.mk hr))
  . simp [←this, hb]
  intro a ha
  obtain hal | hal := lt_or_ge a.digits.length 2
  . replace hal : a.digits.length = 1 := by linarith [a.length_pos]
    have _subsing : Subsingleton (Fin a.digits.length) := by simp [Fin.subsingleton_iff_le_one, hal]
    let zero : Fin a.digits.length := ⟨ 0, by linarith ⟩
    simp [toNat, hal, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at ha
    observe : a.digits[0].val < 10
    linarith
  obtain ⟨ b', b'₀, rfl ⟩ := eq_append hal
  simp [←this] at ha
  observe : (b'₀:ℕ) < 10
  replace : (s:ℤ) = (b':ℕ) := by omega
  have hb'₀r: (b'₀:ℕ) = (r:ℤ) := by omega
  simp at *
  rw [←b'₀.mk_eq_iff hr] at hb'₀r
  rw [huniq b' this.symm, hb'₀r]

@[simp]
theorem PosintDecimal.coe_inj (p q:PosintDecimal) : (p:ℕ) = (q:ℕ) ↔ p = q := by
  constructor <;> intro h
  . exact (exists_unique _ q.pos).unique h rfl
  rw [h]


inductive IntDecimal where
  | zero : IntDecimal
  | pos : PosintDecimal → IntDecimal
  | neg : PosintDecimal → IntDecimal

def IntDecimal.toInt : IntDecimal → Int
  | zero => 0
  | pos p => p.toNat
  | neg p => -p.toNat

instance IntDecimal.instCoeInt : Coe IntDecimal Int where
  coe := toInt

example : (IntDecimal.neg (PosintDecimal.mk' 3 [1, 4] (by decide)):ℤ) = -314 := by decide

theorem IntDecimal.Int_bij : Function.Bijective IntDecimal.toInt := by
  constructor
  . intro p q hpq
    cases p with
    | zero => cases q with
      | zero => rfl
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | pos p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simpa [toInt] using hpq
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | neg p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simpa [toInt] using hpq
  intro n
  obtain h | rfl | h := lt_trichotomy n 0
  . generalize e: -n = m
    lift m to Nat using (by omega)
    choose p hp _ using PosintDecimal.exists_unique _ (show 0 < m by omega)
    use neg p
    simp [toInt, hp, ←e]
  . use zero; simp [toInt]
  lift n to Nat using (by omega); simp at h
  choose p hp _ using PosintDecimal.exists_unique _ h
  use pos p
  simp [toInt, hp]

abbrev PosintDecimal.digit (p:PosintDecimal) (i:ℕ) : Digit :=
  if h: i < p.digits.length then p.digits[p.digits.length - i - 1] else 0

abbrev PosintDecimal.carry (p q:PosintDecimal) : ℕ → ℕ := Nat.rec 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1)

theorem PosintDecimal.carry_zero (p q:PosintDecimal) : p.carry q 0 = 0 := by convert Nat.rec_zero _ _

theorem PosintDecimal.carry_succ (p q:PosintDecimal) (i:ℕ) : p.carry q (i+1) = if ((p.digit i:ℕ) + (q.digit i:ℕ) + p.carry q i < 10) then 0 else 1 :=
  Nat.rec_add_one 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1) i

abbrev PosintDecimal.sum_digit (p q:PosintDecimal) (i:ℕ) : ℕ :=
  if (p.digit i + q.digit i + (p.carry q) i < 10) then
    p.digit i + q.digit i + (p.carry q) i
  else
    p.digit i + q.digit i + (p.carry q) i - 10

/-- Exercise B.1.1 -/

lemma PosintDecimal.digit_le_nine (p : PosintDecimal) (i : ℕ) : (p.digit i : ℕ) ≤ 9 :=
  Nat.le_of_lt_succ (Digit.lt (p.digit i))

lemma PosintDecimal.carry_le_one (p q : PosintDecimal) (i : ℕ) : p.carry q i ≤ 1 := by
  induction' i with k ih
  · simp
  · rw [carry_succ]
    split_ifs <;> simp

theorem PosintDecimal.sum_digit_lt (p q:PosintDecimal) (i:ℕ) :
    p.sum_digit q i < 10 := by
  unfold sum_digit
  split_ifs with h
  · exact h
  · calc
      _ ≤ 9 + 9 + 1 - 10 := by
        gcongr
        · exact digit_le_nine p i
        · exact digit_le_nine q i
        · exact carry_le_one p q i
      _ < 10 := by norm_num

/-- Out-of-bounds digits are `0` (for the LSB-first accessor). -/
lemma PosintDecimal.digit_gt_len_zero (p : PosintDecimal) {i : ℕ}
    (h : p.digits.length - 1 < i) : p.digit i = (0:ℕ) := by
  have h : p.digits.length ≤ i := by exact Nat.le_of_pred_lt h
  simp [PosintDecimal.digit, Nat.not_lt_of_ge h]

def PosintDecimal.sum_digit_top (p q:PosintDecimal) : {l : ℕ // p.sum_digit q l ≠ 0 ∧ (∀ i > l, p.sum_digit q i = 0)} := by
  set l := max p.digits.length q.digits.length with hl
  by_cases h : ((p.digit (l-1):ℕ) + (q.digit (l-1):ℕ) + p.carry q (l-1) < 10)
  · use l - 1
    constructor
    · unfold sum_digit
      split_ifs
      apply ne_of_gt
      rw [← add_zero 0, ← add_zero (0 + 0)]
      have hpqge : (p.digit (l - 1):ℕ) > 0 ∨ (q.digit (l - 1):ℕ) > 0 := by
        have hmax := max_eq_iff.mp hl
        rcases hmax with hp | hq
        · left
          have hple : l - 1 < p.digits.length := by
            rw [hl, ← hp.1]
            simp [length_pos]
          unfold digit
          simp [hple]
          have hc : p.digits.length - (p.digits.length - 1) - 1 = 0 := by grind
          conv_rhs =>
            enter [2]
            rw [hl, ← hp.1, hc]
          simp [Fin.pos_iff_ne_zero, p.head_ne_zero, ← List.head_eq_getElem p.nonempty]
        · right
          have hqle : l - 1 < q.digits.length := by
            rw [hl, ← hq.1]
            simp [length_pos]
          unfold digit
          simp [hqle, -ne_eq]
          have hc : q.digits.length - (q.digits.length - 1) - 1 = 0 := by grind
          conv_rhs =>
            enter[2]
            rw [hl, ← hq.1, hc]
          simp [Fin.pos_iff_ne_zero, q.head_ne_zero, ← List.head_eq_getElem q.nonempty]
      rcases hpqge with hp | hq
      · apply add_lt_add_of_lt_of_le
        apply add_lt_add_of_lt_of_le
        · exact hp
        · simp
        · simp
      · apply add_lt_add_of_lt_of_le
        apply add_lt_add_of_le_of_lt
        · simp
        · exact hq
        · simp
    · intro i hi
      have hcarry : (p.digit i) + (q.digit i) + p.carry q i < 10 := by
        have hp : p.digits.length - 1 < i := by
          rw [hl] at hi
          grind
        have hq : q.digits.length - 1 < i := by
          rw [hl] at hi
          grind
        calc
          _ ≤ 0 + 0 + 1 := by
            gcongr
            · simp [digit_gt_len_zero, hp]
            · simp [digit_gt_len_zero, hq]
            · exact carry_le_one p q _
          _ < 10 := by linarith
      unfold sum_digit
      simp [hcarry]
      repeat' constructor
      · grind
      · grind
      · induction' i using Nat.strong_induction_on with k ih
        have hk : k ≠ 0 := by
          have hlpos : l > 0 := by rw [hl]; simp [length_pos]
          grind
        rw [← Nat.sub_one_add_one hk, carry_succ]
        simp
        by_cases hkl : k - 1 = l - 1
        · rw [hkl]
          exact h
        · have hkl : l < k := by grind
          rw [hl, max_lt_iff] at hkl
          calc
            _ ≤ 0 + 0 + 1 := by
              gcongr
              · grind
              · grind
              · exact carry_le_one p q _
            _ < 10 := by linarith
  · use l
    have hpl : p.digits.length - 1 < l := by rw [hl]; simp [length_pos]
    have hql : q.digits.length - 1 < l := by rw [hl]; simp [length_pos]
    have hll : l ≠ 0 := by rw [hl]; simp [ne_of_gt, length_pos]
    have hsum_l : (p.digit l) + (q.digit l) + p.carry q l = 1 := by
      rw [← zero_add 1, ← zero_add 0]
      congr
      · simp [digit_gt_len_zero, hpl]
      · simp [digit_gt_len_zero, hql]
      · rw [← Nat.sub_one_add_one hll, carry_succ]
        simp [h]
    constructor
    · unfold sum_digit
      simp [hsum_l]
    · intro i hi
      have hsum : (p.digit i) + (q.digit i) + p.carry q i = 0 := by
        rw [← zero_add 0, ← add_zero (0 + 0)]
        congr
        · grind
        · grind
        · have hi0 : i ≠ 0 := by grind
          rw [← Nat.sub_one_add_one hi0, carry_succ]
          simp
          by_cases hki : i - 1 = l
          · grind
          · have hi : i - 1 > l := by grind
            have hpl : p.digits.length - 1 < i - 1 := by grind
            have hql : q.digits.length - 1 < i - 1 := by grind
            calc
              _ ≤ 0 + 0 + 1 := by
                gcongr
                · grind
                · grind
                · exact carry_le_one p q _
              _ < 10 := by simp
      unfold sum_digit
      simp [hsum]

def PosintDecimal.longAddition (p q : PosintDecimal) : PosintDecimal where
  digits := (List.range ((p.sum_digit_top q).val + 1)).reverse.map fun i => Digit.mk (p.sum_digit_lt q i)
  nonempty := by simp
  nonzero := by simp [(p.sum_digit_top q).prop.1]

theorem nat_tel {M : Type*} [AddCommGroup M] (f : ℕ → M) (n : ℕ) :
  ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have : Finset.range (n + 1) = insert n (Finset.range n) := by simp [Finset.range_succ]
      rw [this, Finset.sum_insert (by simp)]
      rw [ih]
      abel

set_option maxHeartbeats 500000
theorem PosintDecimal.sum_eq (p q:PosintDecimal) (i:ℕ) :
    (((p.longAddition q).digit i):ℕ) = p.sum_digit q i ∧ (p.longAddition q:ℕ) = p + q := by
  constructor
  · unfold longAddition
    simp [digit]
    split_ifs
    · have hi : (↑(p.sum_digit_top q).val - (↑(p.sum_digit_top q).val + 1 - i - 1)) = i := by
        grind
      simp [hi]
    · grind
  · have h_len : (List.map (fun i => Digit.mk (p.sum_digit_lt q i))
        (List.range ((p.sum_digit_top q).val + 1)).reverse).length
        = (p.sum_digit_top q).val + 1 := by simp
    have h_toNat : (p.longAddition q : ℕ) =
        ∑ (x : Fin ((p.sum_digit_top q).val + 1)),
        p.sum_digit q (↑(p.sum_digit_top q) - (↑(p.sum_digit_top q) - ↑x)) * 10 ^ (x:ℕ) := by
      simp [toNat, -ite_mul, longAddition]
      apply Finset.sum_bijective (fun (x : Fin (List.map (fun i => Digit.mk (p.sum_digit_lt q i))
          (List.range ((p.sum_digit_top q).val + 1)).reverse).length) =>
          (Fin.cast h_len x : Fin ((p.sum_digit_top q).val + 1)))
      · constructor
        -- injective
        · intro a b h
          have hnat := congrArg (fun (z : Fin ((p.sum_digit_top q).val + 1)) => (z : ℕ)) h
          exact (Fin.eq_of_val_eq hnat)
        -- surjective
        · intro y
          use (Fin.cast h_len.symm y)
          simp
      · grind
      · simp
    have sum_eq : (p.longAddition q : ℕ) =
        ∑ (x : Fin ((p.sum_digit_top q).val + 1)), (p.sum_digit q (x : ℕ)) * 10 ^ (x : ℕ) := by
        rw [h_toNat]
        apply Finset.sum_congr rfl
        intro x hx
        have hsub (x : (Fin (↑(p.sum_digit_top q).val + 1))) :
            ↑(p.sum_digit_top q).val - (↑(p.sum_digit_top q).val - x) = (x : ℕ) := by
          grind
        simp [hsub]
    have hp_le : p.digits.length ≤ (p.sum_digit_top q).val + 1 := by
      simp [sum_digit_top]
      split_ifs
      · have : max p.digits.length q.digits.length ≠ 0 := by
          simp [ne_of_gt, length_pos]
        simp [Nat.sub_one_add_one, this]
      · apply le_trans (le_max_left _ _) (Nat.le_add_right _ 1)
    have hq_le : q.digits.length ≤ (p.sum_digit_top q).val + 1 := by
      simp [sum_digit_top]
      split_ifs
      · have : max p.digits.length q.digits.length ≠ 0 := by
          simp [ne_of_gt, length_pos]
        simp [Nat.sub_one_add_one, this]
      · apply le_trans (le_max_right _ _) (Nat.le_add_right _ 1)
    have Fin.sum_extend_by_zero {n r : ℕ} (h : n ≤ r) (f : Fin n → ℕ) :
      (∑ i : Fin n, f i * 10 ^ (i : ℕ)) =
      (∑ i : Fin r, (if hi : (i : ℕ) < n then f ⟨i, hi⟩ else 0) * 10 ^ (i : ℕ)) := by
      let S : Finset (Fin r) := Finset.filter (fun i => (i : ℕ) < n) (Finset.univ : Finset (Fin r))
      let g := fun i => (if hi : (i : ℕ) < n then f ⟨i, hi⟩ else 0) * 10 ^ (i : ℕ)
      let univ_fin : Finset (Fin r) := (Finset.univ : Finset (Fin r))
      have Hdecomp : univ_fin = S ∪ univ_fin \ S := by grind
      have disj : Disjoint S (univ_fin \ S) := by
        intro x
        simp [S]
        grind
      have Hsplit : (∑ i : Fin r, g i) = (∑ i ∈ S, g i) + (∑ i ∈ univ_fin \ S, g i) := by
        calc
          (∑ i : Fin r, g i) = (∑ i ∈ univ_fin, g i) := by grind
          _ = (∑ i ∈ S ∪ univ_fin \ S, g i) := by rw [Hdecomp]; grind
          _ = (∑ i ∈ S, g i) + (∑ i ∈ univ_fin \ S, g i) := by apply Finset.sum_union disj
      have comp_zero : (∑ i ∈ univ_fin \ S, g i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [S] at hi
        grind
      rw [Hsplit, comp_zero]
      simp [g]
      let φ : Fin n → Fin r := fun x => ⟨(x : ℕ), Nat.lt_of_lt_of_le x.2 h⟩
      have image_eq : Finset.image φ (Finset.univ : Finset (Fin n)) = S := by
        ext y
        simp [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ]
        constructor
        · rintro ⟨x, _, rfl⟩
          grind
        · intro hy
          use ⟨y.val, hy⟩
      have sum_image_eq : (∑ x ∈ Finset.image φ (Finset.univ : Finset (Fin n)),
            (if h : (x : ℕ) < n then f ⟨(x : ℕ), h⟩ * 10 ^ (x : ℕ) else 0)) =
          (∑ i : Fin n, f i * 10 ^ (i : ℕ)) := by
        -- reindex: every element of `Finset.image φ univ` is φ a for some a : Fin n,
        -- and the `if` collapses because φ a has proof of `< n`.
        rw [Finset.sum_image]
        · simp [φ]
        -- show φ is injective on `Finset.univ` (actually globally injective)
        · intro a b c d heq
          simp [φ] at heq
          exact Fin.eq_of_val_eq (congrArg (fun z => (z : ℕ)) heq)
      -- now rewrite using the equality above
      rw [← sum_image_eq]
      rw [image_eq]
    -- reindex p.toNat and q.toNat to the common length (p.sum_digit_top q).val + 1
    have Hp_reindex_p :
        (∑ i : Fin p.digits.length, (p.digit i).toNat * 10 ^ (i : ℕ)) =
        (∑ i : Fin ((p.sum_digit_top q).val + 1),
        (if hi : (i : ℕ) < p.digits.length then (p.digit i).toNat else 0) * 10 ^ (i : ℕ)) :=
      Fin.sum_extend_by_zero (hp_le) (fun i => (p.digit i).toNat)
    have Hq_reindex_q :
        (∑ (i : Fin q.digits.length), (q.digit i).toNat * 10 ^ (i : ℕ)) =
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
        (if hi : (i : ℕ) < q.digits.length then (q.digit i).toNat else 0) * 10 ^ (i : ℕ)) :=
      Fin.sum_extend_by_zero (hq_le) (fun i => (q.digit i).toNat)

    -- helper: carry_relation between digit+carry and sum_digit + 10*carry_{i+1}
    have carry_relation : ∀ i,
      ((p.digit i:ℕ) + (q.digit i:ℕ) + (p.carry q) i) =
      (p.sum_digit q i) + 10 * (p.carry q (i+1)) := by
      intro i
      simp [PosintDecimal.sum_digit]
      split_ifs with h
      · -- no carry out
        have : p.carry q (i+1) = 0 := by grind
        simp
      · -- carry out = 1
        have : p.carry q (i+1) = 1 := by grind
        grind

    -- sum the carry_relation over the common index set
    have sum_carry_rel :
      (∑ (i : Fin ((p.sum_digit_top q).val + 1)), ((p.digit i:ℕ) + (q.digit i:ℕ) + (p.carry q) i) * 10 ^ (i : ℕ)) =
      (∑ (i : Fin ((p.sum_digit_top q).val + 1)), (p.sum_digit q i) * 10 ^ (i : ℕ))
      + (∑ (i : Fin ((p.sum_digit_top q).val + 1)), (p.carry q (i+1)) * 10 ^ ((i + 1):ℕ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have rel := carry_relation (i : ℕ)
      calc
        ((p.digit i:ℕ) + (q.digit i:ℕ) + (p.carry q) i) * 10 ^ (i : ℕ)
          = (p.sum_digit q (i : ℕ) + 10 * (p.carry q (i+1))) * 10 ^ (i : ℕ) := by congr
        _ = (p.sum_digit q (i : ℕ)) * 10 ^ (i : ℕ) + (p.carry q (i+1)) * 10 ^ ((i + 1):ℕ) := by
          ring

    have sum_pointwise :
      p.toNat + q.toNat =
        ∑ (i : Fin ((p.sum_digit_top q).val + 1)),
          (p.sum_digit q (i : ℕ)) * 10 ^ (i : ℕ) := by

      -- 2. Expand left side into three separate sums
      have raw_expand :
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
            ((p.digit i : ℕ) + (q.digit i : ℕ) + (p.carry q) i) * 10 ^ (i : ℕ))
          =
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
            (p.digit i : ℕ) * 10 ^ (i : ℕ))
          +
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
            (q.digit i : ℕ) * 10 ^ (i : ℕ))
          +
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
            (p.carry q i) * 10 ^ (i : ℕ)) := by
        simp [← Finset.sum_add_distrib, add_mul]

      -- Replace p-digit sum by its extended form directly, staying on Fin N
      have p_sum_eq :
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)), (p.digit i : ℕ) * 10 ^ (i : ℕ)) =
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
          (if hi : (i : ℕ) < p.digits.length then (p.digit i : ℕ) else 0) * 10 ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        -- unfold the definition of `PosintDecimal.digit`, which is an `if` on the bound
        dsimp [PosintDecimal.digit]
        split_ifs
        · rfl
        · rfl

      -- Replace p-digit sum by its extended form directly, staying on Fin N
      have q_sum_eq :
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)), (q.digit i : ℕ) * 10 ^ (i : ℕ)) =
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
          (if hi : (i : ℕ) < q.digits.length then (q.digit i : ℕ) else 0) * 10 ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        -- unfold the definition of `PosintDecimal.digit`, which is an `if` on the bound
        dsimp [PosintDecimal.digit]
        split_ifs
        · rfl
        · rfl


      rw [raw_expand] at sum_carry_rel

      rw [p_sum_eq, q_sum_eq] at sum_carry_rel

      have psum : p.toNat = ∑ (i : Fin p.digits.length),
          (p.digit i:ℕ) * 10 ^ (i: ℕ) := by
        simp [toNat, digit]
        grind

      have qsum : q.toNat = ∑ (i : Fin q.digits.length),
          (q.digit i:ℕ) * 10 ^ (i: ℕ) := by
        simp [toNat, digit]
        grind

      have carry_at_top_succ_zero :
        p.carry q ((p.sum_digit_top q).val + 1) = 0 := by
        -- evaluate carry at (top+1) using carry_succ
        have : p.carry q ((p.sum_digit_top q).val + 1) =
                if ((p.digit (p.sum_digit_top q).val : ℕ) + (q.digit (p.sum_digit_top q).val : ℕ) + p.carry q (p.sum_digit_top q).val) < 10
                then 0 else 1 := by
          simp
        rw [this]
        -- By definition of sum_digit_top we know the sum_digit at `l = (p.sum_digit_top q).val` is < 10,
        -- and by definition of `sum_digit` that exactly matches the `< 10` test above, hence carry is 0.
        have Hl_lt : p.sum_digit q (p.sum_digit_top q).val < 10 := PosintDecimal.sum_digit_lt p q (p.sum_digit_top q).val
        -- Unfold `sum_digit` to connect it with the test: in the `<10` branch `sum_digit = sum`,
        -- so the boolean test must be true; if the boolean were false we get a contradiction with `Hl_lt`.
        dsimp [PosintDecimal.sum_digit]
        -- do a `by_cases` on the same test; the false-case contradicts `Hl_lt`
        by_cases h : (p.digit (p.sum_digit_top q).val + q.digit (p.sum_digit_top q).val + p.carry q (p.sum_digit_top q).val : ℕ) < 10
        · simp [h]
        · have Hcarry1 : p.carry q ((p.sum_digit_top q).val + 1) = 1 := by
            simp [h]
          have : p.sum_digit q ((p.sum_digit_top q).val + 1) ≥ 1 := by
            simp [sum_digit]
            split_ifs
            · simp [Hcarry1]
            · grind
          simp [h]
          grind

      have carry_zero : p.carry q 0 = 0 := by simp

      have h_sum1_cast :
          (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), (p.carry q (x + 1) : Int) * 10 ^ (x + 1)) =
          ↑(∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), p.carry q (x + 1) * 10 ^ (x + 1)) := by
          simp

      have h_sum2_cast :
        (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), (p.carry q x : Int) * 10 ^ (x : ℕ)) =
        ↑(∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), p.carry q x * 10 ^ (x : ℕ)) := by
        simp

      have h_rhs1_cast :
        (p.carry q ((p.sum_digit_top q).val + 1) : Int) * 10 ^ ((p.sum_digit_top q).val + 1) =
        ↑(p.carry q ((p.sum_digit_top q).val + 1) * 10 ^ ((p.sum_digit_top q).val + 1)) := by
        simp

      have h_rhs2_cast :
        (p.carry q 0 : Int) * 10 ^ 0 = (p.carry q 0 * 10 ^ 0) := by
        simp

      have h_nat_tel := nat_tel (fun k => (p.carry q k : Int) * 10 ^ (k : ℕ)) ((p.sum_digit_top q).val + 1)

      rw [Finset.sum_sub_distrib] at h_nat_tel

      rw [h_sum1_cast, h_sum2_cast, h_rhs1_cast, h_rhs2_cast] at h_nat_tel

      rw [sub_eq_iff_eq_add] at h_nat_tel

      have h_nat_add :
          (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), p.carry q (x + 1) * 10 ^ (x + 1)) +
            (p.carry q 0 * 10 ^ 0) =
          (p.carry q ((p.sum_digit_top q).val + 1) * 10 ^ ((p.sum_digit_top q).val + 1)) +
            (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), p.carry q x * 10 ^ (x : ℕ)) :=
        Int.ofNat_injective h_nat_tel

      have h_nat_sub :
          (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), p.carry q (x + 1) * 10 ^ (x + 1)) -
            (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), p.carry q x * 10 ^ (x : ℕ)) =
          (p.carry q ((p.sum_digit_top q).val + 1) * 10 ^ ((p.sum_digit_top q).val + 1)) -
            (p.carry q 0 * 10 ^ 0) := by
        apply congrArg (fun t => t - (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1),
          p.carry q x * 10 ^ (x : ℕ))) at h_nat_add
        simp [-ite_mul] at h_nat_add
        exact h_nat_add

      have image_eq : Finset.image (fun (i : Fin ((p.sum_digit_top q).val + 1)) => (i : ℕ)) (Finset.univ : Finset (Fin ((p.sum_digit_top q).val + 1))) =
                  Finset.range ((p.sum_digit_top q).val + 1) := by
        ext n
        simp [Finset.mem_image, Finset.mem_univ, Finset.mem_range]
        constructor
        · rintro ⟨i, _, rfl⟩
          exact i.isLt
        · intro hn
          use ⟨n, hn⟩


      have h_f_reindex :
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
          (p.carry q (i + 1)) * 10 ^ ((i + 1) : ℕ)) =
        (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1),
          (p.carry q (x + 1)) * 10 ^ (x + 1)) := by
        have H := Finset.sum_image
          (f := fun (n : ℕ) => (p.carry q (n + 1)) * 10 ^ (n + 1))
          (s := (Finset.univ : Finset (Fin ((p.sum_digit_top q).val + 1))))
          (g := fun (i : Fin ((p.sum_digit_top q).val + 1)) => (i : ℕ))
          (by intro a b _ _ h; simp at h; exact Fin.eq_of_val_eq h)
        rw [image_eq] at H
        exact Eq.symm H

      have h_g_reindex :
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
          (p.carry q i) * 10 ^ (i : ℕ)) =
        (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1),
          (p.carry q x) * 10 ^ x) := by
        have H := Finset.sum_image
          (f := fun (n : ℕ) => (p.carry q n) * 10 ^ (n : ℕ))
          (s := (Finset.univ : Finset (Fin ((p.sum_digit_top q).val + 1))))
          (g := fun (i : Fin ((p.sum_digit_top q).val + 1)) => (i : ℕ))
          (by intro a b _ _ h; simp at h; exact Fin.eq_of_val_eq h)
        rw [image_eq] at H
        exact Eq.symm H

      have tel :
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
          (p.carry q (i + 1)) * 10 ^ ((i + 1) : ℕ)) -
        (∑ (i : Fin ((p.sum_digit_top q).val + 1)), (p.carry q i) * 10 ^ (i : ℕ)) =
        (p.carry q ((p.sum_digit_top q).val + 1)) * 10 ^ ((p.sum_digit_top q).val + 1) -
        (p.carry q 0) * 10 ^ 0 := by

        rw [← h_f_reindex, ← h_g_reindex] at h_nat_sub
        exact h_nat_sub


      have eq_after_sub :
        (p:ℕ) + ↑q =
          (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
              p.sum_digit q ↑i * 10 ^ (i:ℕ))
          +
          ((∑ (i : Fin ((p.sum_digit_top q).val + 1)),
              p.carry q (↑i + 1) * 10 ^ ((i + 1):ℕ))
          -
          (∑ (i : Fin ((p.sum_digit_top q).val + 1)),
              p.carry q ↑i * 10 ^ (i:ℕ ))) := by
        rw [← Hp_reindex_p, ← Hq_reindex_q] at sum_carry_rel
        rw [← psum, ← qsum] at sum_carry_rel
        have sum_carry_rel' := by
          apply congrArg (fun t => t - (∑ i : Fin ((p.sum_digit_top q).val + 1), p.carry q i * 10 ^ (i : ℕ))) at sum_carry_rel
          simp [-ite_mul] at sum_carry_rel
          exact sum_carry_rel
        rw [add_tsub_assoc_of_le] at sum_carry_rel'
        grind
        · apply le_of_eq
          calc
            (∑ i : Fin ((p.sum_digit_top q).val + 1), (p.carry q i) * 10 ^ (i : ℕ))
              = (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1), (p.carry q x) * 10 ^ x) := by grind
            _ = (∑ x ∈ Finset.range ((p.sum_digit_top q).val + 1),
                (p.carry q (x + 1)) * 10 ^ (x + 1)) := by grind
            _ = (∑ i : Fin ((p.sum_digit_top q).val + 1),
                (p.carry q (i + 1)) * 10 ^ ((i + 1) : ℕ)) := by grind
            _ = _ := by rfl
      grind
    rw [sum_eq, sum_pointwise]
