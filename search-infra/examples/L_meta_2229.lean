import PEqualNP.Defs



namespace PEqualNP.Outside.L_meta_2229_aux

noncomputable section

def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

inductive Trie where
  | nil : Trie
  | node (v : Option Nat) (l r : Trie) : Trie

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  Trie.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := Trie.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t

def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

theorem All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (r.get _) (l.get _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

theorem All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

theorem All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

theorem All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

theorem All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)

def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

def stop : Cont := fun _ _ _ _ _ _ => false

def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

def fuelW : Nat := 1024

def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e

def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

theorem stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

theorem tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    · 
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    · 
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h
          
          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

theorem runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

theorem runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

theorem runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

theorem clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

theorem verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

theorem loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

theorem loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

theorem check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

theorem checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end

end PEqualNP.Outside.L_meta_2229_aux

namespace PEqualNP.Outside.L_meta_2229_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_2229_aux



namespace PEqualNP.Outside.L_meta_2229_aux.Link

open PEqualNP.Outside.L_meta_2229_aux

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 3
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

instance (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 1

def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]

def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l => [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)]

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha


section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hp : M.pad n j
  · exact Or.inr (Or.inr hp)
  · have := hn.ord j hj hp
    omega

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in

theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h

end sound

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨M, hv, {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf⟩ := exists_nf ⟨_, hv⟩
  exact ⟨val n s M, enc_sat hrows hM hnf⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link n s f rows hrows C hC (by omega) hev)

theorem sat_of_check (a : ℕ → Bool) (F : List (List ℕ))
    (h : F.all (fun c => c.any fun l => litVal a l) = true) : FormulaSat F := by
  refine ⟨a, fun c hc => ?_⟩
  have := List.all_eq_true.1 h c hc
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.1 this
  exact ⟨l, hl, hv⟩

end PEqualNP.Outside.L_meta_2229_aux.Link


/-!
# Generated row file (genrow.py): no Monotone2 circuit with 4 gates for one function

The formula handed to the checker is `enc 5 4 (rowFun 5 fn) rows` itself. Certificate:
CaDiCaL LRAT, trimmed; 883 steps, 6745 hints, 1 segment(s).
-/

namespace PEqualNP.Outside.L_meta_2229
open PEqualNP.Outside.L_meta_2229_aux PEqualNP.Outside.L_meta_2229_aux.Link


/-- The function. -/
def fn (x : Fin 5 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4)

/-- The rows. -/
def rows : List ℕ := [3,5,6,9,10,17,18,28]

/-- The formula: `enc` itself. -/
def F : List (List ℕ) := enc 5 4 (rowFun 5 fn) rows

def c_Kw_0 : List Nat := [
11408395001056476221185355851738942846696599572453596725965810280003803933738634752004045227799836763448248179672488761031558588977348479476509011739698826690070752259886776019093261756663862977499041933807105366352765736490498355391653744009618226899099543575931490675102260201131064043197756145401755344897,
11235655759110569411318214857627900170661794882482151130591355509707159651029688448435084556054324067913730826575702024413814450404032295816028019757792426906466844561674050364884769788507124301483420661743520019595223372423195074745896245829839456384326343760841966819918393222089974603412154312431570784320,
11235582092895501861043039447289723723597153245651115337619908931444120718417624944349091899620122701251976866198043929389627290755615126652974747663352247082172415027563785649341898915348472457235805105396709159533462186331650366679419896406374175423187339054036933943279689295981358312031670889669095063552,
11754146719651824213102418708180878214170268808112216399971971013899173895305442996738849132117965682180420236420303013068847659938048883343426999730254496477427241855280413953442851789868554685860334577721766332489072943289371448450318702679268692418182393150559506268986786192560771869610928836996046520320,
11904889229292006585509244323798177499024850163416020244029159788492375821186093418578196120328593752294613316632728424738276906305583141727268110845122287648685317677075155690598611164947592394194148107324757407739501751048616036874919936767667379547254384640063234841320220242068294127813980177915399110846,
11235582092901289797940603025561421840947700201272271406369700094647333133790883874455026617854222872586560111348616354709495743312834995701956814808771340527902196481192021876387055843667012034735814766629893428541230567920629102499790103160243502853528420133249304941262536417697158853400398194171898232832,
12124334244857159127090966366513557751175573934132227128993914895955092951311013564969903049025769599224647414664539457132624638863876470565794299523487067879422308051676291320065691415036598108811532180596901467438199760401436924501604875291768056704799908496986513265709542112818148418409550589714738708480,
12261487354739110039669657776302535493340455129369624935858750569031646531941062943907252987186701620267867862532921290284359018731720420481911258079526154941779475254638280115238781839056795818551771362752271994685124242628343472694691201938386211142985925496425300660851282820382389429900537864185956007936,
11235582092889478527084874987173654894236581462687680942043419397413665856758131712716982324441100502453761773881189236136186001710556546883791990870912347020927459384454238451675648193773450353450722351264731989949594222830054261593516391046705171122943020841127648631953850155321861172019224216381079683447,
11235582168589621690038163789953498963931491153878028112871920000493528603037990993969043248635814629862930310390369093156886543186889565558826409658167746672934475037742557341943800368186057636557351337052370292449384795544147684395002825172544574668041249806472705265286685733611783388715472183410208436646,
12645859531016631511864712147785603173911754672323240538503131111414216079017595175987766347023572451051269292108619506379508340177146064186594002131455579253744041330461469345473868518258431003130432630334330000801237270962130898911966087083486586898891590812366054856594214689313026248014265284603223736320,
11235582184776046267589504240071614175523888335111447356827827243895724834300305974025191215886782172954081865372402578380683744325826586107006465542648999219578313302808446092997689986683535205322653507740107177137248744744067314945203006422310706664622037628811339731476458370667954635718144841709204292099,
2322569102819073663986672530339537917332162090925397429815056522066477337806108222342299648]

def c_Kw : List Nat := c_Kw_0

noncomputable def c_K : List Nat := unpack 12 c_Kw

def c_P_0 : List Nat := [
19999988754458491720658394412352612368364139269034223868950167880813232868164476337482929131341616175401873493650531811910835377467524127019028425159343448478744320658164167370706929507288271742863095152604313489063909535714308120090505421431773697511251900737374683689167215913137657335666948508014453088830,
12573593051360847242043872313899394217679537961864958933954476102059016804184753350158427599435611073753390625281607009526487417496908387914342460105472566497489355216628240232283211344715415169518121923062150406008941946292374109463677220335027186294782109920190269693062972184845762051790017365960598790630,
18200521978236985938083368359085073028905464154482773866155513889416906157536604223602605179401908736391191434555508434460804459210619659694649212113380809180237902077783427130657732556216728148058034990535443018716073181754715892074606160859963724788275515934617322506268316943172314674031606069425797952088,
11482803321570058774095706079176784243450765948731286803189674114896439702248510550019040441006441391181588391898689246330558015549825066546945084026630973989379000281814948334491412184548016292679856355060037003143190638184244364190027262936867880091380442955597329397463203172666305246813081675580532302290,
11236731956733403135299762344231145225996512276253394058574586034653257276863698528654063922024348185867930022662686078411860899314145532461409598722218969833106639101486944193217402173944652837572410550037394687292969279614331131809771611685997372664007152921768928284745962924494229227550814708602398683136,
16560037718524485721301145749231846360315451820591706811079915658396892530007982919182047167509921695710404648891460171850284555990029660994681432767942780241469079523566452571481993987260918972224465405870079739531181562943642143188242339631267564262623350299347183596585722779086990413423588253766545769050,
18197887406449346121051234782211442726975604092899789527553969334111562250573278508190953707899183734254211371262893171983331040016032788493921709577314813272530596391833658518450980861412868150749732989947198414643544366583322320459119415203484877905567944343180134320994042011997814951975953700080723165442,
13071022586649834457531956652675118450752619796200145078306353825001315205490940396420566672025830446543481100298909610913784433406992658336680521726893414391420094047811765417844641010007850469260659771235191474951863158422043156073427729356158671123981688306426159767381930618756069598892877664969233605069,
11252605127392975286634306354565853691321559284724671523915265115181840836774626334093044147856170746754978911648976066268541464581430164450831409829523072934705440259028969569198872029098106974292232892615812115755027517708136368970537520450563527324563143931243551020865800220058161151100556918026117238791,
12655772426551891242260571967178699057380781643586205652108275499622766533844456001329687406030447183386976243200888475558912170167952506686575791796209791456037401155465258345615507953150890635131657797433268076388862747036973815023096088366925207583129855959558530751795648559099299092069700768581071929775,
11235642517160064720297548248164564461676095524733388754457477008949950002205723080707389065838585098402066174035052209536031026014515677133623519584738966655451046018920449665634913304115177772114039106108590740290997606293620511853470679351300175895407096528242400989401325403324669271409481715897212080819,
12873667036841365768119181916418435653375257461399520705421713299791783129326318799913164487165841673804443032187015425790447112237549662195777834572447286874953443114026634610847392429890066723704767237738230013975286416699131985583268993650330698419842648756988415870352660312736856360434979448376283443821,
19769665300568935720661469869551154395052155336047133112519741235872612499368547058986489370171052934149896813657150459276635107240714603564525290179351960669055466865025017697575776176023024017953621971092766930311352136982007894321303158496372053907269372509124008901085190173546320883074639811354215244787,
11713560081309550141112004827186012093266644477281746708969784403949729293858042287531064793444753628197010136282869346599099005044360605424470084950327086037108453071515541479753417875566340903125100339159121376683190095314031097459836801309025788070986891922751369720839576156171308607757003470908381016613,
13276802493827050637580291531862380937305917249090889856640636127055336938099871476423548961547045745783754011765548081089435328885697061962875239404666830425849039940052719218262975229091554243499184712479780321738891380533421360962003104013217513283835412902403028457330320929826581207425270782531236982784,
14250701681424764735378673214448427601131273845046038665928044639424976242695614889891276617527474545887414816708082168924720103586431849705873417081362227171861424874282275284348029013868406867638812094224977533081045648634185748735286106455545698110564588339290396644056670442808806842197786934701157876228,
11339818520518168395666496824776513742935746782822161781056132954502347814132167464560411840413394478726214258559979333812934052654656099028555167006807466260175223253070348329594938850139151253443625417811909651427260154171934520566511489955637666881232018093894251065460614135646339970868959689141031064291,
11237013365578119165468508212945697220037558207562552228263272513847314911230940092656148224778954493553463058359189312408339083854214893698970867726136778893741549979932995292785218341510271567650003005298831639543434597606376656595436231008831227110398567376126012627830425675803532783973375073083696779687,
11710701762256449875061029434086723738446513876113863329824357771000036213286114335558143028643844768187616894231308992250149644279136083326386733327958347776882727028414865988823650973506756442489324462026535991157714248799127345510777563547859097903572390455824936395854004624179282820396704394149063848579,
11485632378631933883510080424352828590973362604746611815546186931307385078620683622901892141901777462953040547493577870806392961753502500046967798399186443376803988627482721616536207656208335258698775245868443329015271070727945652706367531049584244161077959118592492938892084881565402469049637260989288866637,
13427712741254260724620509687842375549216576140734169074911024449255239670908467813822729287869388782003497662751455931326813767545240560059821822502680732468408923324599032959669603078880752744942000706601817849753980981218180310260696514182807620937924626406414377072583957225210257202453626357211113435821,
11237170841316977563189061355507033910744637068006937007119719331640966433818548130918938316206196446842242490148772697311520127107896611811437679696818257378550148389069833524101072133333236997871668368487464964335656400761997124606856622153979437229535371982044708281645549139262615161362777935942978052699,
13438996948568762340698503599541786541358633469362510113114901052319875752265288761925875040357007259829289314195925971432957626636095337983579032519742562899483877406401271580328933400868673883412784212335252974494716259113625776696717316961103752779556606047329942157052118231831794500703283899792909222690,
13484893375176188529139398859359772513637598611869890637180305103984151936478027346829001281531265289083652264091022981866422649979046500591855395357093478606875333520042236860185579676118440698839240332899902930730754906434181200265076336331997670164877131496977730033134430050852630473863048802702129955634,
13529218635781739078016609654722547855385907851160295557506957523886338344132659705583449233852594227607848467249752590292168420004355339265850550068249943538479016117133793389695058580303067803104486642052373536633769492209845044499786943098651615561008543591090279800860346688019837217896709015791265706242,
13109187329753148819207513426421138000724855369411110429734510757499468741996595058125851589793497871805782552524627658835508538555701465956701471815605678854606795874388048994998642285448835852093299251387448469557012028770023695615605003201475017774176496102824863882230002103403712738267146279819648200961,
12399662469021207228426448927537845473064030121406318593239636365503002383916666319451726308971824239609645551861977141892656826160068528230365114538957170627363963082297389147246264786355437688933265002912902205491407625428175819734453890400407279959916740925834019167238711374207279466049822733922441261201,
12862789900507900258771255794634513894243959609307679285217309052704189408317902918155138254821100321472215162203869780430867989398914508063490268733193410679170249318237154973528184682974854086961010219109394704274716710104586698482457175945299975105531623519571354992631365049996329051915063762686150148351,
11716186518167212782180903595822254278956494977374784765028796055383871184775117752594110329552785635955487354770436317462559496187808851162912970587845630826509824149431752147610622567462305449986245426027985555418569856370276720374102549444946194519264873073153633553139210901981577510687900939742418936821,
17751325494007108813364524187273102252783642093320889829358378788837393080328943616903768761570740443081005081131632407488249479708391014908099466706126923733637633970407477852912578745753408962094692417212351167578390302000998691754299413370414607942217790477658097478047786138961958920568414608178195862226,
13564441801788316525268922083618176656553850062881554912784860790155915768146024391879897677038855145664967253559083833169523380852505702646746497319246422852948605192815775379219017197829595279529068767676379820985600351705008260849806029892353108456396768245237219616851463113220927611067146542754747977728,
13691175808475906750190053737745162983357372152970414438588617651420585533482447027119952669402896651204951278700584339250320565438585134497743182570437114354941273807013984155250381626413972462195701996127661795807163959763129574406640010420080437626589946372093889217320046362087528624966712977772856463535,
13573072109258073437435664746277033853338082980113499082133117493024464025575335983872188355517214040252995662823475083797640609160865698997834860630872151078302050362779247849071514730893420367194611158038016296943369690890067924298142910542822650878381724616964002764919028837471561082642391306698091397211,
13631241088715734029905505551769417182183870445200171264815143639492272266324414237837649649486376925286138118690579973329535823590771180598542332175915602644544583865425426747001340995293799308965329087792904507678188679613382652980470677672981152133487459720297202288762783639107364127992596516463915147860,
11238384817107344982891231013067674994130811368926584371492884946744303446887505174027158681614284341347445965945861943296194752529896366046102231286523689571576524215545338692745089153751815547791230402983463570139225455900380783561684096437387434714064301616030604182060025788797127959248922016187665532328,
11236434626710993572366219239127640097453398443619096269204693048524801137267170406116657462741666503785670507159346496948846374572420084907095467048428124559003204833147803908867980135471093797573775239522720548308587643895046399653534463510042986868334543092535843440770308308051957240426786837724970070921,
14039386625580517289799522008626536431745535393768812554475730030885410918435515602279383373794380445117381061083386378827344321497674731959785439075143963332776445862255382950685036709461763330634351672282423983594231745439024706320289448457454187300482665210762719138929020916047751578565370675476058563307,
15177945263355185667976994069591296418092408457200421130272080679357639158966169950637353445317928979436001863428052714674299939810048755765190916784120109890001283020978688678854336320899726510824173627859489272633198981464209212433165698649479448496683903989164089060930703182623492122867137580570628817914,
11842137816710560394183907834005442794969071991695542433896391383439480541872448862670369267004574823365537852915030717506464722136596391131361856127553392320950195654230914446137206354132404904279774316969658752654952794042031089306705842529285920388103224209876259858350289261145010939728373429745399157637,
14039490511860251167744384537062691467104575310116728218233675644774594527144401312543180349543884346940058721692239148626784893575993714450923108617085385847161994382356421052802717480576666603076739821219242486310800842820171127856180688137543941036846958660315592551687980042733951297741922841791343838117,
12637334423884612173901625143066446397370424096351700381746804281003364337533480260461533951094333240185652173229464165285183564164415537113850498548217233190293053510240729544227430399020913820435772536772022946908932080670849279273085955725940100363823059482551536536145004224191569314088971598842844926839,
13730614806188565555317834416289660839566292121177539169151447827316761399447443344597293368214183215461766157857121809678981914817933060407523386334185582825548459688496149133422304380835264318785925160439681602021225909789209294321325986157242210805863431989004056398701308756098648319763287106408421527624,
13578157278422461462183410203461917899106297317575509760172138931943846517460007181717152551154196628731142303775347451506888848770622542927127385549445228786860902269825281050522539030147287423268645963954749660997591565789940018097175856948769883130034663750106038394534350372156852922999044447507449825010,
14025466755128227674289266216245522322368375883658460002787102045350134383991485573179465874823106247656582985466329654479036175676045282200156102809929904900122151544041767047670200808935974707733291403715117241382209182672056697305208861093869628239449576190247727558485890161656905787561717951673287414353,
12635148615982344817139971451493323979222347845379250729802746243280518363148249780577489150067996795242007500419913388471943649593738436599111159151387607736673496646537984584555386626966487286596036441245711804181909224575099967321122174207354387763830872352829575254309057879790514302072883106997663150365,
13622107151198603872429329695157742134156931602840319317439219612211249766813922914989675847065880540418893032678221226465320409975942832163835652880497827286709270058980347767369567882064169852171922623131018782478863243827793021864237791776648823108395811003622312588551098953882072536876761266936058868505,
13639470274819997958543806311094224680504968328947638393493337568477742045023004912356073343797095528993057166772570500037616907043360703033492827057310026066882284792580077843928893045469101233830142374080285506404833475053961657430470582327287715095735943187603338413201645634550234924551017674341481038761,
12958571411875341056376327009016280091008199579707429093247585143453197595056200712330538662583900483544407693713199414185664294175966084180157791488691340939602042948010108014621619357811650734109577160987802157574915730693349325720546716275631982632479950396466612297135237870297817600722818669356976235960,
15211128835766850642776149491618055350701048350579388441453531636051508122359609136620205330734186667658360057852574764087876141872635117611681930546611236668792126940487338166728462004746991752130031938563155584605524748773336578050769126496880204444599131719562742868338912374155063582490109178875530445752,
15175600302677562712452644221329008521934789238698091002272759345268326766519166837422761388703264339364451604041668440595571549600385197383670748205256568433955848738704623695736623581945964325387773701744432561053098728605933313281363202596871792977384750494268020847166393859900358763095413255544258954659,
11933844109369328789060569636779559810784670793756658344438676536404185525227913663759831869419924756023389409503515953076362174976963273634398938368319943217469854101418765657532684181573169087634704925445506639885710795436266630489945884594922314507421296125587540229670922372145978729690958169665860964952,
11411478947138919369089212370210599795991607066987053028085148399565440197847347859548422759040028096510936047085150218913608132801576605215025236971561700426426822858252387883316574405195184290553333859527131674456272843892602656476121859789208623232246476305708604115963562434887545453340562249166460848369,
14039562754634788298346812276154565751522934349784136902411042346839279676655120207390550082536482627387659312239071721857728428566262309112907541250130578185553579065026973786768203515818169134981014737200275649226908253585961701780754606213897916293292888856803945006392913073018422706324627152207920505343,
11447140093788375350173867408429183707492320661280693238608544083735606776296129175351056141154656882793185949468639229552102036444689392112077005975503289033543652735354995467037568889805849613571300932774992474365507972446519973921739819366218721601192936928579078391462104891918597209920109373814533873665,
14039640044648570757256028640848831547050847787481707547602206421294646371072041702255261988404471377002111758432586267688079706741903452850481870273587552522016356318598984753175023332914145607151119340488432573159185406824939134418763372178206400877472037020493416427589861718092132545835201114205757075969,
13288993873940240163233802946091648069071216067200905591437436050241471393707761384060357112694934893785121532087109221630032810685739566850492199479006299088633296825322664605892255899718130735286317322681938506884401264416263733106702955247033151642666410639197494745609257677374871088588201983761200571337,
15421995060014928032339851160414318622546373851507530571878906534803179426326212246077350554295144753262093911059542270289661607759713013793360085697159612114047575321154751679256144151101439515392749092762367806938153961120835613181482005462590099607099551540800820824437702092821398481319798473742528210428,
12856795542330195560130941631300019784241629423011735826264123311122757764312688417919123994636340454282525367900473159474383004501591535378921496101142857924817297243975803278630969006015886819708692399543101329057025228710902477536701052604430037959660791129463337649746172043566500957530132334511624548776,
16557207490665723659899259036454276636462227259452976022419708370383594586086370344647591281569422300983878360625355953863772909252688283426166647295860162434633481642169274984967934223681580640600665446470470631068009460653466299977896530532592065333924869067891730470056534555430495289863166096014777340002,
11705330957639770749110936051015858000152135383511558138797312526037263468084459225020151584273859998877211919974341196549415963943657728607954846430354330687147424624088645004246690364877530618273986427055385376800033295326987656409411775355542515349627500090596321992595347814161980124461962806218022228930,
11483705411958627590094165931006189023051609566519399408247349204622550964649348991494267690088164838315770521195549903300794372195815826310004294980370698864837025981662205708464464250863343525564264822736104631460438778517969680917082595954763144459414091662331986313089181916976736691677522822576689754202,
12637329947124084370543076478238599740161777878663100482878431061987924778826101400638340639167008880793060246206449250118918598934466172266291019694259937747802808104779703484697690751795987486294432134566126717843484870923780914393959098319765081974228223822041462176711535678868501651158152781167958778448,
16634220480864387797838236921364348327268014662249242729789301107815044945460873140926803322750996222347679999812691685086652701885945688770625288931735805017220570057096033052532851860222447839628781912401566804587485684807474277705719040975786779749648571133351741685135755224690006299678997442702501490754,
11932910560800873361351345943723352888485589493262961578696199503670794790623230491216824455095145812452195698239961534299395396452571783579131772754870979088714815834127839901268350958282998339289844152556630549398871472330568924267701022481330773899332839586965554479258521326900626453334372871629206062024,
13666106640958739366514644142730805504192401712975645959841469636961877838010033841700339648541038560713925082137373147012836755107960104215932121084319745309132498978941074135881368044583297439837119454060034206342386822942681152555662940223056605410142213456509776182233627542545753983882756848275490300651,
15084356325675497147372474353918157972434507749666802502364367978568726853521650407561565905906661640675727773293795410199417710942551185880192061951556112903354987407047109457869523952196216057947835202601676748903739793980424749609337038692849610309046019264624204638716476107981463143505954718525125269817,
13807083862068628041483234366520592054316970747976017657714878470708769359026169794269089454363512937708566722405792502910957270423161641075870309118451830099953616720832620343792502513443673663989272905300099202840598114883369078689555691835970002251079137092675850221826255945150011678582550790211989434530,
13576995297746475261964211763365092567492424157520415912219182491604087269216469458564529660322358990061841839192459755534013905154329782990829172607134828009169251156944011147540551423734252356312835591257558967650017810694381853689769814550837498510545474475546655176159027508992219183945434278302622681233,
11584409185584705701617843881742671429694409712040247657464514970629110454451968759593645394578113052566387126789947457315342107988651768825414860884440968061233981897127902992022485602820531097025123526667742151380478611096245712144349467893799269718789804864059952153499911025918997505457189605872976167932,
13682393739438850218872125286317031826291857343359592444330276053444493377799070983238132484706448820218259013177242425290368465167831108220970415937188152216652295128139095008574717857790441313505912852741002075621597726086711833555214959159896246942356449144680862889142547086511099477259526520913834813332,
11238383583175136910178403468822000050305450116778406496624330822982281476942345396336133973369698768354170777958222800612258447937354817469180593640990221215686665047740516847256528455632743136593877209696862165099112956699042300066884823679236120311030734647977239141788797484175462755762944717397979240811,
11932910533311509651160250188286315693648828923891783387756828579419856582074194159806027025512715593144650681255921635977794856458990939806569346366186285557929827762036928819773344639189692431162219876495199614449117257046635179089679049472326171367555399890941481427131041536080219247333152397162836267096,
11235695968841420695798497436490340181027352484807801810656531001683468747734492571022124371794847797209177042932031362320611021071354336949396407621841471934016710809614029409916166393508014797583656188979921686920884168968335922289759908609968584300085475394931999324020939191980819638376622196374228000769,
13690622853296365382134676572044630774190002906680538753384094150597856766223587154770764615199898598057728678157858196469058616384233024402115140614327123991177298320068081852194856559487075019859430266871396511465367687574309027589996900577236604486440482836441950685847910135796037413077663485080635413495,
11479775115589857303876606439936624319125519685461559102576873575744206887670386487980913412233615359781385489964936741824635684234565348840149978549749826412895126231595164642865419990496239687146100161587166050646829877268627049014934851600452727114715227731737159077951681928102019967341176414444834967643,
11585284475553174178898220800925487546458238441426937741901261048714896682983557047371648558873961809648112850627561402402212210455552890054117754461112823937113166662825311810907306711601260937191288483875282149953844950316421884721391675451308643819262566540383017845576632196636355686145166170132529414144,
12860441351177348597176086326037818679849673421050653232929093248252295123623458699958703463307997815400881581011716358074022131404688068295014169348203691568174333056380875785814257156233946843087786773994042063228935649132233987813260834701964232320319405173439341252441035798872313778156180734712565101229,
12882118106834584983439621365364820767161639764231117675062424341296507052841842709306050400627311402103566400836619981180514070373113381649448188824567611104793003749117941800805100100568693828812867446074421227418777015254405716676767886057489381502356900945179047752837574721058160119938059934967464820909,
12642827914902517827538941571307042846879062403213569884555572100842712348344038592678583145596156664956900795031046203504081369267044636842646528531787644019130386818422974321104121465827452712059453013589065371901228148071642407898441024735453404059110520522146963152963350904079638718868251056059369738330,
15252011798990647298890812203438045224095739458049525714076128418173039826936186216401110247883045467839788016492130942922377315800035525288135066163954208516181165325987923671810850232390387276146153224419927467091061858739597525577961041241383401543595007181350012403834993643725407505707256500424420634707,
16234147097686518826398563602270241908501555952508105165919898206203434492893043924616686385016876623333324176992399453154677384778231573549164418919798263245466046292652137693117814768072568597698619260462312023025935185506530205951253052450007857071651272383929214628357596890896930699569299452757406360430,
11704913817648075735902470805716111877666774988624456169890072105959754047247618109100577398593081048163886473370317008349238098971948545664777100955126657687553498986714345221151794504544155477951523226087326063675525011731265530523146559974293993016600937145805106411313537807899828885534414102435108751084,
14133784012241846234909930036688234365069310510233871855368983229774798326616517080640968690717912288339968146150791251823777563678819214736681193787172726737913181414929078135741440910767121320431645782746029760987494392155240001273684806678659382952279089565216399234486008823350278721809721875322041451347,
13655135063085199199958483848092778748832184407585977081793272278877213640734548838218479068232878019148382201570269493488885869623116508119009709176255449879781751523863496197715524433262798069374310789622679810685996065787981009492802434838309607135260954317422666389201636121446479833631741046962792112383,
11677215122147016790761172644211341135788766598463132816515846405996351481429474797273721346672615551258326369447873342946292676121909544184228186078096608999960395668364684676269762201965604653599883033334166319063987027779309523105372317979909197569856154955788723652798034006633243881568829754337351610622,
15438454446715476530073635411112312796602308033923734753322118995161098990548951291631635139415679160926952558032050841639796544313053801906240408777422063166774956620362803487589815575851956806805387773360743845792840399629545677477602972391131266938365718358259312103372658990282815290518717833801017837510,
12004554306375483710429404191856598039431258615622215834006925696549074594699320093025969115002961876172287709877772590520202426546406037625940415970312493948350717740020179120121457733173049477573614474569321058727695781773416207966409520722544417283106003400019079294764517316415377421573419072844771639725,
12291718569886951035325482474790376642722333916162901572633702467320985270506799032908362025571486947743350260926972767218065993203959040350667393150602278739099688813777257351540194200155877989478890047449117704451832856558472848347632557621157669120514090786931235556697012704851388050110601003249982109030,
17712544945882667388291768986718081803746395521041146440702206279362779325510251917168573323419943741408975195185460319349079701671180363384897507220424276218280292723325209972320039680388275462321262743428072421146505519343883354061424416351842423794586362277894078090550026685858478128856722211031520781691,
16330949949755332820395900229081455874903512264714383229257903841969044733312040632083595728955815934462984000377829588598336665563852737976444304533571715177374069820555570856505572348463251226513483434644232918041924129860331811007567729817393655286419247957883096677731066702114233465427862673772013802342,
16406327999528427567012398457054291501895144183784188562300869460018637251053210526053516630187371227083940812697249997209135370981772125571003363692466895185216617731811559833158853423771940367375858399026086809615202608527206133596391557914798454194090406505002039376193010198222797186753312658776423138292,
11482573748551995930327780768191672101538461339138815529550149792748236101969855183475762858312179466941604555980774859320167735346570271519523132519927300878655961006208585302988184675706812192744680818328920052453679749292748135616433546811181040055232625114260270320440599020778137551849600122434456658996,
11483926616948776455464170500540952088576068921210723105879339101379129593523372285752853574002319385498106015553576111696838772339006551992102985659498596455711269828799021071604453228812345310677961996019607089542844041505338501704285378630913577771752794632988490782469601222615103280814661434864597321166,
17251513690302748697141410055895422248052772276534598452412814084529085697593847880790585697815443146821205825788594421989635791752180381969970872961796722362310576378564401550164690546746942585662717327795558108689519000202025953882827998152098494995387050345463595560953550331466390101719760212864935457705,
11482917962517373844327159057676777743934711752083494945082306453318274459682876271641676606277493305787713039856975986005085544083661445424320383743904160745912744610310724413150509948224876764350059974794952342587613088608840799952582643968746052969469089825635683888054682657749618022339996869178683630158,
11401356587987460940588602498083047229764441784449779631274992384218167369607696329396926807498337375031537746252516950626406405486542042396379406410229100841546702047519977960566500799382246339315645468356055358844409143724957322704138989036077054737886930157385326507569243467774283073102712805329247110138,
12879406216806160711804320086282995937994382650363756010632623611310821551365792236143933329616160898769829941202871177408641348476718791686581782370457700851431281373072713289485129729528984434026299135988819926745684647207409215271719677299497036857417159609317580648908149048659326608339449283105431540225,
11482516297846968955605747735105900963147433397036826146531040526322962495374931369026427097266318357252962048318766154418085267330356771571742566416838124376357632739150780676278673633644649468013102043377610524188456784286733909556736585033291734640573742760655314709477268794524445601950329977369274893373,
12862282474445357655179358850231371141196714682592008965431535452150336825554439419897894684791770782484958348010094287206797849254023773565679674229145405158834892724310113946300882170704165872315938613789200218487476837021721700527046026335662024616387981116484934516771619801634916494499895617957475510108,
11404114385227916084190757797194257095057825993961600534126762436613236107279892553503707522791110235131774370216552114516653588849751280546711648438513466197525193841320152256153091446850897314225860117610685965681800370307315904174493701880618007524712445767716938106435313508110067600464606734659239620705,
16340685371223093585175594661676026841740481767851396657849302513823861140127440127077466230472352024276074748020518530405882397466104541250158694374429211404517919178695037568973378852732232525532328143140808057962263187932949025638820163057649929858062229802677610131153437974814547617277850276522914791939,
14259432432206958050673555866407414375373465514986784493397274234013172903741814222393885851996192507208233748961873872070912210335452530373568866103960516871357987815831933985873656350308244651458306889628670474872595199104896873667980734689055513910285106178815423174316694883156003920513668873711726834080,
12862286285900512480527568046145899494773187774585296155814404360922084374170729951201106039235872085641482454471283610539248768949649486814651584645657025829318696465287423512977599957348099616238018967776464791887815007917665377448268879179969162717142214141994749663850218330795662889185687883599821976575,
17712544945882667388383996110038320795483856483812917832759621980303401898071623149532125049572789785738920156547063359018517715849922503773921642402171770903425828751425651095574275987656350766919990214039589432631158769739493474586770693001379813084157273978943825131510989912867684983025197237925880022096,
14031340417208003286596934837223079675511226737091001273372325233035561453361461095970323457661049765135741462026146558212371433458246629662723142758702597594000253528760226582370681643504321738268686172317086560545748538314931667090374327848943438254075100742652971471941939182481440478519516237482092512334,
14963743113901420708524991831927216006243307189401985822549199449845770511367417370786024823256703822305776703495344950637841750945193406895376436211241534972289109197522010649485566901768308820197342455173574767201338624983704968107157943022414400295102250222805470772988138294340369982016030960732429635677,
12221265584101141196255764032608064550019350336151727346406446970587755995690218458339641429389632322687139786180397338454926516631931284750143099520003247138817862015522177270462068586065612850291210811239188903324854547512236700172897635184158831575982274225677180819310206550180491240830271439176427946074,
12646234642579417852230351699373492008437146084741599265005672060989835535784427035410558365897859134383209205116045625052995936169516196002512886831335964141114850201259610599723031003943299860959015168787267663496382676931113132238030728353346082436459470247893871336638993782279154316643875633504876597337,
16568831067087677886217841565581140545088981387565372360868299433762206361362640098788067110003011316729304155370607279608197381297371503628716567862079583045392734025983528719678803266036883709669585691536518538079958242510092732590788906869621031303309072503691224770876240547610042935181800499272615313474,
13675466939400455546483782847585186977225506845550776881064656701276575653616245300153780519693848532628632024086539938671329508173337659160856055426459660036212408886349442598183921129927987575491002270726569495118614590626670079581363932608916883298623517802447070639837524308571459900989068423832603861864,
13800480525564993627798180327791169714642751343852207470169214177376387875198017670977807373089228133723159954516163038654226012993882962028397165496774824245593552046709937908990611755431114749329444931065350885306482947946837843776043017876867684281440627079148768158794032661780682379793259638248997108029,
15082109872663018100230758719212756221643496267333314958445126886205488652106907360261222842780971604911438370324877416129317073883487622917593971697497894011830430034270271348629349596063096740262226679668887439321208088787652175385883113540568188610596645653064174469280288310100754806005216156141640880327,
13827836803778346684175536338386073266262829249879198487476115247306263819670879552575235923453056801314662253072915815212192333020842614971564141893566696369439731594640541568035847275055814075015430843435694372709344580835728421895269209036574729420552183365540586393970691460469441743378420746275269211884,
11477605751076725341305846478731791801126215594928182952640045792294112145649363308762540271162639999792987458185443769296205812087068210269210013862892281584177728448024711628841355846161318090197603179818127750167133245488841947101180780810470034633908013181151036329580674075231123604666648014784017430844,
14329815155496289462439749390280553624617654525320821268977843783664214799944056250020082992596963961908379452519569982196010837019268757610823452217250606960865353570146142701464649691354505972910973362715560639606493301195256914699148082238739822422429933226376525164496500982792029663129275807440635933039,
17493471141914523753524351492389324982682420348543274398700670843184987582611349114269918826462517792156290721586143515220317801558549206461117796904904633133232009811323466684058165206520611401608548004147081147661191113661044964877071022952790348447628852720386105962363090547039021483780843979848740742277,
11936034158791182582863881744035402333110222734324334642662221709766260454212516450322220024249129847838896996671300591655364131501977102660457491731473583182606522608619721840096700493877318932865729922797486858755667210498189120270567450930852882435252194025774577958637688278695537185773537790290894520490,
15211192622859130335384144206231408827764791490340630662457250628535759497462680608279808397947164048450524333778794953215928246456945136436762795957815253825826626156991999491174410490341976696447438611116868503991387884388885447150243712108312092144172539628845898166292786888853999758430733138132776964096,
11277013984553975721696569857352707961867322408003159497785877597816373103249567054085099193445511099557106224487306983330502949632758045620643316396373388053768975368445209010774031237723123872337652359056304908136362339425781476994661792938333258921603810633888710840247898465288685449508072618476336857088,
12401394842354680374605889576331792468201827099910977600865026822888473204889099945778297536838022387733759203423969591974709411420128944637042258590823229092832592058125467318779387228787080830250376122533125715812387340030080580034656578194657550657860698485942837138452110245880549418595302660702175142317,
16006569262861357970681024448629762409772957339350574116518050909005745526930667538855524732903941566357490575624186598885235040526882435065403037923905762116713931752776747526130659140815036174905058874578273365938236514053695581897923876975321563854056611353418163378321593671628800203342313101550541262867,
11241927041717884486333993495912729196882135897166195201294051640831477264914130081892288647599104371122764907748935571775985481921260709564470419923343418557376511703037280192280453122064932072139037389109477002802560666136176382612649963102584996130263151644349794253286836349998861445081388228405466231133,
11236716092704107736753142965924787927613702340780153863365330803303620995866324571075270077470758148492846674514948579292727235652713578854077445187910729003520940376577070384642007186812314839017156214450082452086084312905540925905346924507645916505369073068834020351815302213000206793532726996395669258240,
13690622655747968452204788624956450843480602521068965642897779041013637860079022598502914826836658480627194085234216467221499146465957032832585978761138375683074925788068539914476263481149075958386500630935811866783097708082576933669328203604513105933318908986903992569280763507782508763565986326455217976502,
11235753073880124808933646451999153862714420733524813871694163050747504189023036548659954159166709703775566364994980299465307693377941671046587702320768931834438424653024793556953075996810679111316911256807345503670201275949953408633015809547982742040178402631149615278140136687772188850649459381212666089563,
11235753090230128545990842144884012688638995517448830071135011584368556953134205869735003231285415574500449947534462593689674930922713379273907244098919378463157171372626749451675819593449845389293549662578805037800132119320236665617240901575159855355419924058516103163177865120320658292851296245852332344044,
12634884224186072462464413702233643051327129536979920749343285800074647352503283072916098532847245414526292326269693229803939889737878258580081252917299802074506387609979380853942745194543744022454137707639319912517595880661998461002494995386879284159432538117244836944366197229624956372585615103057127850734,
12870844959826058588632794932670374467823627917947215544541464604258278100753594382946496594133940321664984836351234227054383997793292548957768819368312311569691511336944434827455756905306204204561815741037735174385242035845738121149591786656609242748383981840357112976932715209963235436568069273053707641344,
11485800264742179877813739870069744064941765989990576928019541438121147212631367194811668059712327090172106867093238441905226844240152200162383576881105689809561026645357559299903788474578898442246322009866052223343091766325672834382271554039223801585501851449451786841232473852943554501632794321826202616406,
12404546418159552813427847976935043213781547393397297706808231553491362078917789190082867769254629337136476644380765491899175612778800534388904366515245834779610781144885850294872119512924606480249572507600062644080648416098731362643178479630079358479734093478615820359065040939964296861060124393537141367416,
13562268149112593401516399382123276149477960508543482397707551321911553318498478638670106703796746653099902836516652107154523939242103544209442841862532623958860579960204353776364841429694559447703577538615398263380322374100254353702417520853506171082530597914484791772725588821754606001333487388775590965266,
13568053552609858291294475581133327132697893990089699682458796429705984956116709465822162445788368520808504924282899805417616711639850214830270045750232940033991946264508865649511207197598310601106600362870493466257351450311367445949905989218741820130394932396160946969400990991618494276001454688116346524494,
14790772191741547178786718884042127143772602724019423871433349900144841137836369455812550031106644286928718708810084811816255997197810190662356048705591719561899930220620445387313280259700798029526259161143243041005143757588423303218843906417461227020968008765834905283234582521775220334232311155775997489324,
11853453510546851505704517884980167666033906644739728200976980361513287997131519894220190201517958126770733529927649711295329428858551426721824933136154761406933837044645338869698239882043207391826234649644177327623000465818658231534904089691954102455434949962680418800005874949578071048370359394069900173575,
11990605275173516898774596797175363269152510875923829986603909796835561777837307954636489733270720902198578356228032630366162697049497264870990350531434359858396150452998186915309933595198958459876153083081187041552666618573773284061626479342346323082345423661865552627507657548851962695953115119420999345059,
14508113558100158510821067636147543580841030908065131621719205533546373205972981946741566014532136305605619459138736833926871185337216944493798965465952844838466289963427574184590580119004392463671631444297051723643801410661134562514784149807378419079944423858662229441933395399548300666021346181927522116599,
15085656724402507460621848736915925844053296009087953698202851560417821905400841307906991909048186087504087341631048218336992142028881247452103292716357891270264071157164701881187658804793043001373256143601995332571211421950764710771833570277902592692523313278463085580252243220203443569159978900800993175280,
17499517105396377987495631587521452683649276178472986808325898627643435150026032700571599721680867539609527646930400043105241269352865973303323863104471036066085914269867721453148937774944240609695802031881709612120159492795511695654251603956841562518337704715718231722456400423593251579082093263536094795109,
11401356716187438171947872429806184140991244069126598944730679692486585116963121178724213233055055670350190292694782707653247418512905853518700196520649253475923404036398719319051404196781394681360948106872878008761866766903439063908090058295485831278130789902548068009569422161312281683466388500522147518705,
17037273621840205534958634925672914664961165306212762264361253690782420703207138552018954982385545569161113525321121023780752840582184203629872417575123923570474946711281751753706840118820021068240708708176143492160749919628213640568602349399543160689467615800648474287208937546295026134056411455645039186433,
14377578353144131767599284561310817136141431866781165699362137365581897133994196874735025289947426007051501335883252729056615081100547876278582991323722790754097532186083819470473098151775631582695346827390598502069447521486270468448337794805633202858688770719663537255286658159973984584748547692174189277512,
14780805796141129711219301099450166925136638348725550473744130034213399643856247952800356320730388119252829453751035461026722659074926455815223524082181500413669924206761720186734712710559690700822282316865165793195262654071306898665555713022546973974540988400676277050374372947435535487316400784806322046706,
11990605275136480271197724078996485274049696070576223152652426089834748511303573992405734635048006855004641324439595528077151441300098080511057394536870743683288853190206443570702571350905679002063843414472043228631092784002810966651938347660091828991865307674228300860047498648242477506881173521822202639662,
11485800113239640725921283907255544491117197330017460601081178113001717727230925385468201172729137269317181161680278182927095327328212150563343879769574203483150376443024229908545014877761337856357080992480272059359347892062243712473857130617207427497584533155872887606380436974682482394399541634368892150775,
12865360176053403102946719906776427890719067621769452982191225884532687360763347795857669735043165938249547043057048597910554357548522323303570481230719717921477535712351188505628996259355346160014814041438626981663169814907523834282667234609910445485933552938382896702741693749980078196118482397279508476155,
13792174390550191035280457696582765461840726861437820990932422372088058802329415472038805445696486098104125509957736869648265437792237169088189082226290449889215227704193475716580159298720812726284332217506987803686668169201313062385251724170732731725724915195903311048158124211241313161170543053300577603755,
13117914099347543475689690743595882320878928990577995392280007964682841106239280134862564931227997810657572609131414541487830555096077684150438518647697723763229357163630350585104203137662399721081111265892686284819324516271897676809122836268936896061833553472932172450767249285217479268746515891562952881493,
12862286493393068956546266839100691996260101139333856387038552147743384736950654083860259747336700922815823429005755995625254403187019548455932883659968016507563813310212978694643328409801804652539780605016819169071645206414925870482894580035281710729790450757324605203031852933321191117541458969889019532598,
12862275079822927618848349671095744812669107048065971326486425786259370678646264312514318136777378050712124780509817808970665868089099091514000861946035807560862458921791963242680406913972453851175425630043638023499485368305502533583189648229379733982636803583944902488618376681420056536815152258570149793897,
14665277764080995778949988931715290881748209421122939349971116215238592264315515004847594384655201182157781655927474874635829573424135082700298098737036588081665369612819229063709789342985575207226200541352531257423490880998170047818748617897868469104039434952674713681368744843230696737718684885004665065562,
11510757014780097761200205696450780144099542751466443536910798082209184536648181180744617862963611692809431268294735868827028282648270570225817907563561862262005002285124147398945139848374843604031365921928460645434407533225681975605844457988976936789105804326084715190911739797638186935582737334071886456058,
17482161219492537751694265170685919370360846384634943607184960408126291655258865233433483225582965178171641085261688139391656606071357457593960983376844169692892620984584333629916084598217651733380334971351850878253516370017068495324952914927195196515540652633559752039443123945406089486532561986918938501721,
14714600714419130657212508242422165081634844219963714613225162485474511770984300128369974144141125783405994895872772384179129827812390932597455377315882443590748589384323423346661606671460521086301910851765363181814176255421150867344935255359587495172726852715827229813534595240315538045410979931452825335162,
13795324032305116505508649362241954234384183451945204100803224944426217902173048702723786263348429692239025053597075932159872672797757451419932335515032447851860261107512650683175408216528859062755703889670461885440579326342855295221919349975032209677855271465134750066408937123554448875779620688918553182447,
14041927440540895932284479246662466519501498989684617400947511795748896036503311639248952854425645763283413715483536096458181605246975018456038222469271301931550373601176408284129073599962589608674447470717122226573924135555743270334345500548588219020988196864664227765787102365324885005099828776396834271593,
17515360644898467225138389326287626164569085141722318482495503069786514668828164570227139261914589361002779727751486353557894381870361908359257965115368784204258488076932655574282060352905001932686559395533649135876797263779245798072444714508977147161312006699976380243107286613536518237201417802954307506452,
14959450422639951170738859589919578545888742860325069294951692283195674173403053483283340047769252478172024568456062439303105925438050094431874489175009314668221061800986968817673315378943033199982992497194107062762252751564323292939165551695104215011701718888021562109088897363837703294547908904115682415614,
15178194203222006135027040265340530062619274197427280675669601361978028520767708892899612784629428266104381030035328026175125058973778853265347694572572544623769690380699885975599831090669078469657880172531910090578073170737868668299632361763394151563891563930930185767572625359268347076644115257258289869487,
13655590499288460828866585816970168352320512920014367226620178597096587125724064378369330552136984911164357739153620163189724829894214064671583082109555368536836691912267905890202451186146757682368007731599855169917743335140691422244301222131867921197273941001125312104047687174760734295801192447025663881617,
11732643580267481079516529503369287909566988997586286207542968347534839407973033548509309588188685515159154179963920425755032590288806812583726247583865736156264727384597288537848147763906225499306567896652974391440528734694766728636845441721316087028971145274828533534974161844828998743641249771320752312574,
11422455213055329356454348856708719917991453221755800263228117936236417745277204231345740426537871189413990172366413475275783120409154400033472774837076078123952315361738499311560181305294578154186869507833504124088980928483920127872045283594984314918096037195433203249479191233856961745234920953197758501715,
13120981892613200691734438267315081275157383008352119632156025694693655312826801721509907270300526960397203309767084650878196811522475997125390590107067629247204245273290135597348812599929524569290616169424853913819269677280527353265757236070134803400121129929970474425061528227884455545114286546342965658111,
15315275816376001861309080793400104671966119715952620411309532312705229763472459429980387082423780642193899969452710544346799271401547235981523603087369450884517132001133273345228528892806922725092081672387901041903010999921788472733715878103156337154566360018830179423410613607747039581817709424797776181507,
11704919170464161569173633447452028761524363041823210982469176976510883875184897591043601982178317546826451443671708854263751911616962688897904299754024114695858612888696750463558125455944779966067529779059458172827606027661024430743945608750993270650183159289618979527496407335829810417382982197066119206107,
16404296085158164813405709840970292399532570929284023415449812784466582186005606929357944844208437860051686416663069033095909316956525349670015499347906443749982591648952939379620164126742694866813940964980569000229078838852348844979741257841338773293355877874661887518879450034286612269654506883862335177876,
14366039573426247259646943047913254721325407157721506076896280862916050205360960032122382449976980584515626921509509904242890470309798664909675908070592573877315894591953881638319084392966898884664366570266321581318930624160494717406106080788278163542391919305190003881779071614021809652637415127960229580910,
14993638168397025718835510027945285262060546443744338766788955523910675837778935473303798323416415414350456271733057223417511318824929659080060930619805942315440475014594269002558272466482866364997943523484142368029132533901559628520539200602804432938306066606056069629160978460424798221727738663074045912817,
13805988806235333847616986061936866962754920540346521965960343790612507058257513492350191798590376924765421329546362823287473794058627496931967928566385294865474597045683483310161142083901491660741505881634619757368855999684732339164258160454935007383099151319914357109776034926331146769200337437970737510659,
12648293278817813316383753605955061429589693201302727592290701832618441056837101560540687855773178236579435381525382782687679789516687933179748119321155189609142691082357335677535606000091314760886796853213983471074399635379189950052893853557213921623122766398773516678954380519812533565405338399756176557352,
17478951574772962274416324117781813244668508563830643796344144288918388710842855896478987072074996608698003738563528334853313359681908200073142996129132301530757603087776714868722646794218628824320364472331491961111804901738407102155083484041638763172035933037250957967907533679031755692012378772495050331356,
14448559784054568310252835323933389614321794843675182368859105100967801055844204881979303427655291638068408940743493483530607826892814617190495516840697233129526409870012906258392151945310496709980706608858110721341244546803414087666367087501384789710901154609614229339818837013858356489593330987121966974093,
17564743700402053780209590605660745359955938333027072043315842736127659886684940503059843658888048926087421090901597452928003451020472985063396576011988589092410813613547495704985247847717376296560770899445381219578560587082912490328906961638149514002544654866363804145492877642627314839871176085222120302834,
14709182160883023720682740742774102906893262947001031294097863679275897766634367011904831261657334909208804930436221500550519881521208884468252122564984482576302438708310814439289647549995191423418960093461457886547439856875547377579054905687772204336220055578583727671759524440246178255540979370391883478369,
11936313963450588523199743693023739972267935151250111849937613922663501983496080704433939981051362155013196540896517130710569128203207664773475744689967473385369079430770942024484100873829374829116882976661542025287359942313983501440238578891744430008918417754337534987804931318658123080365943380300640007442,
16182518568704086394852261529922720742322761886954231292046650760318442369008674392810134211446688332334331458104984293697610520107330098452995249855426462533575570760462761526850356451262853787789397749018497556415780731783821317058569909574655010407970215487869710715646514278303049477842012587104777806839,
14673553828528749560694740333391141025560015068989390891582513218018949787367529707597164292202146750823100213927832788239355282891671658365955065545727477951453781176601471105510119415594284059979737145354655207526292431337960298975412300170386838529867216129281300920657378710501921867006504637145328963584,
15040399707893645141319060357660549539500386057825323257398626243966159140187828373362968243374937928630081409789662545881829229504060447118786278611688596908444359272191127070095200097407150547028241384059445520797757984407678588819274836812378650900873029484741777906689293644626007038841458194452575626574,
11941407134397658953045218252013250613206427856974455011713443609192663238771278722052371630613941705391986999105546442379125451624079881406734984597219022914896029602305514326450200560549289065110180396472730119885160633318669890729742885706844266535756001773016896388869496613086274060869562136136609956859,
14985596572178188004333765222366762481345494214844956933582025459087483354876293450757204721826507401447334445746464220873572092358194990575428834037388606125651255470356517925954316757970797689530229402223622608528420576232218237805824035210603484149464028615789181239131457046508219194702179614304071315456,
14459931160905594822783183018109146391496724952299260093943011075779096499335501213305708342390356164610927570556572100147094015692390076726881283812743873113193859911140436205374447335036192035135815686059834984820877632059042782797534187954869921413829223521364162040004868489192631262458229242365526811877,
13430092808790815062046855305266379511575826319752078605066433488961730175978203116271975884610003945096131824734564605899119740144085953446601185836453967473261939326486172561005625025160913376623187638865684448608532059753909879376777890107636451721713117605311118025491513432762439361566629659439478130547,
15191869483059722434160646664779573188592048674150628307792149935755715653755509212667403196865846181943263759685343129352850493816467526125566040399070433146219822763085976673613939862557832286119111578085707811169546377299027763307086458494315997394235322542823847029646530821197422382915541549925207253595,
13690622725722775965362248316153845202113570510630677709515409603571132571319293663435262717018099847718057848173233287154725891528963276498910555517667642437526176989888617771494362509945087940359788896159559020308590856043394240913310766189276280974434511942365021751047085324452979857442365049786724943008,
13655135147598746866007905538067143337952265232373728043805027918030214925978044482970455644467437227365907650660474378596647315724838945816395376886172171531096875284572349555762183145011746802602579039524025328509613674815587490412956635247160736518286129627765199070222461459334253475116647307111979135067,
15186586809110669119178569498632046371185260601154802326882022664957217194453720737763352965495863438117078000645113042225124001495199657332801403955756772743902308860550278078672715773274645822824592279744756735181211212510741000394898369919226991133333353259864491221503038659174333403328803176317041901822,
11935904060831467167351640342421309214828651889659485852899015961825128078684325450479633349516988408293762267485073151778481858151285324727270536535907379768586523985822230936955253636327871401286474103387349494654016947405337582245561544508733047319331150148634219270737157394115407005250575205941110007196,
14429758818144234066242201082153484107061609466640547868559841956745571200160242992403936846745370407981908391528489687688998523431643293511398655551054357684421639182174635873276703475982599463238148444775375281798871861068396553047467077445233783512597743528860161074210940270878448014313723233140613317490,
14747635048845905099724476053851775900898055146734897722656962316654170932099248527137522536090729709405531955523778736255422826414081272642321302356037676971497179937185198698613678679453732426162447064260780827747520835758070029243691984699104235401101125281273781782048684069452911729484267897305512175425,
12884232791254525274064804726713162690002188870911845653143372572832823694179682654783243445649011127888559989014478418963474636958272590488329708319016294746487108002495880706541245819249117688827168999646713681493785332706135933729051199921481285670607051193894315728795323108466497599382473725471833961768,
15254282722472365023004946961000386959365819015444287221416883507458024236929565297369826019655541314107101048301868214135057307484882058477356623436819691559883848329891883139538483506318699726320817505208618993094684872099815968469630573274498564002219016199091118455726839547323842783969434018623762288762,
14716588302558674783764406400149581328365509516227021605249524029515899364467205618089001679738772523740051778806706933670311613618797410874762693425990214969313171890178961751555983151530812431361553618142465744220347531128689216319321193270293916638643267004047479617382562955147698870762506099428234605987,
13690622627926468427606029325673496122902495783252313390721146763044691037237943173648428618565455370014687255116186016104860766746818748195774981446296270387311874289411936347254530626059474681889170953908985724423839298095046071611761782340294169152005208430625083856739413545307001488874053034242110698811,
12878755372212605327921080045417055481465752798250130787534955777087949345412775677750971019411742448682807638236510727724020547722049592917998508227306661183971490892420647567331743122223300683610097445328691135972908846782797166822296820494433223465111525317339193686997039815185457760717008138908974096475,
11842200827862110168213445024848811931020583196102109353927603035279786076258774294932700488375604593259524864366934132195975187028820251010836832864338833086409569571679185887057719532114925120942240236803816912566452308309457716424150204265935573672456577503245444152248885665857995658810398308940186784881,
12637329736034193699827396771291808488281844093750291936761782252926492552328145050410870178774582434028406569438817085269312604869908491717268754635018700791399772880620824116197491134426630087265394927761960259884074010443541022839723557968766890261578185618032456305109707685577225494403680905441896265901,
13803948139700637955205196232641958680768158677718342034743019108681436765533694911688305404707136442579040636087036314756050850689851772803807189048267986313928708236259225510805444103862361347033293155873896849156404442236755363747226060064214946868466921057180051149300314675706543671231210267287704580162,
14492566636648701760826741171769985021588857434859294555685186971736071637304694747174813765876903280318778988001938735890342109057553290355782371475911886685063296317295155303678499219473342267178287394472833557490339469053103064211993452550592494320426976085010087949740697137642569671547020547486708094089,
11843287048999653562865942000129478589261984887096922716453014775603823483572216631139911030839081516905710586617999463347626640369375614179529951679390326993523443477714159047730215526880806847647245834148548462184958774951920683395870234100047743224129148530904378760170192533599293730139899106569592174008,
15158845945231949210593501023958252786360021270083678552059457001841628813276927019573005883550956399261389261405810840097717334044616263409546118008869066537435620495735757102501050983221469287568810186231684519948601792351923810620538106700073620584186104322245787002429744063129396947254451530467309011877,
13430032011299491485060432514991988447142938486412708058945970296875625416897303210334426375731994249959406998633191882925753458561586399033951320125616088293388605609079458280156627349416143276793010820438669903586332863739369884862709251393180051982774070729821893466279738631839469752374414882305000026799,
15182887493496049066261953223379610575651264464373163283327507279824506874819720804905698435299719647353458497932539272529520666298238033799511964034050289539559467318561975785143048578321198989545250075718375724455415922746761320992109720414171956459945297537087799593702045910611541618747128730648562795099,
11475182885513792722899778263336491360160660113734987882667212614369861087781714584407253497545130403689452757877707674524868391070546328210123856627214281104452129181722265928173284244879633773516123174238107384194533969369198474161796688357262877776737145725838269718705873000175632292319232371010901639679,
11521729261282939789941994333038056971821747020773268375539332821849770146480138750930582587812525744211738558114923595731654296326151396457790164508681291760381857999362807879971392554836303094101531591337119311598771311919130388767242132310990865927984241500473855137133023508391711302930098285435443713386,
14037216347481097241630411182403148792638124115359328307572947421316559787554761496251232788304761585276350647206990340334738853287461579189396552254775956386610467836912012961958611274531906407228573884103667828075057815052337475003215786274844191477749006734162419880165610445286998404035326555312949883479,
13542502103561810356303186717733971314054671367370527218409175613798064939973643690082836808295020773505020292831435979754938572362935943913768158267507241916209054675932303213108291359242995074056874526467814669464847660646239396314182407123256826235559283394146151680546058705757013530889206488097547284650,
12029266166071640358345445957990295102136559842509872884016546814376634758884575514037767336453893974718029739281093358737035180451259970129870353561093508788762045761095099631623993916296186074125116462439628149496463068035476850646865069953457823489528843850998350807630754185168256973700228715115961238609,
14890865803923306832042362332642098954982036238773358451389485763185789648007010432300994305432495655790741429245006656072025637844106204185788103431408301838809683760522043420539484673148963013162348966347098525441215572600425995050036029311595599983402643796504921816899109491957692089201707137737638437887,
15189095967150322940564713551868587909742907130923375607783333700433232285012016109444089886186593004547658853544767596770228679533510104008955451785327814918908783834791521380448802187040772141569417473919092261435983461827873408214011164672900712590727097070923723576858488341956826166309192466256796513658,
15084291835516390262772117555386287347189162428051361456904694237124413304680689083314387945021098723257862478895041160181552925400524880576477291350269048064772190235695603108436098901925103227007051101054131292017278044706438861736875324196964424465486719035750076987521142893177911684706986846269645702276,
770635514809653733480936533393424434835701162587231218376481754344937530249331961449368187698125814836695735978781599015675967618160451980709840609068412971199521003052566428725290072118040578710811205321874987831833275298375908846190527318802889356253770801320340959435311895840052]

def c_P : List Nat := c_P_0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem unsat : ¬ FormulaSat F :=
  checkW_sound F c_K 12 c_P (by decide +kernel)

/-- Every circuit of AND and OR gates of fan-in at most two computing the function on 5
inputs has at least 5 gates. -/
theorem lower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = ((x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4))) → 5 ≤ C.size :=
  lower_of_unsat 5 4 fn rows (by decide) unsat

end PEqualNP.Outside.L_meta_2229

theorem PEqualNP.Outside.L_meta_2229 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) → 5 ≤ C.size :=
  fun C hm hr he => PEqualNP.Outside.L_meta_2229.lower C hm he
