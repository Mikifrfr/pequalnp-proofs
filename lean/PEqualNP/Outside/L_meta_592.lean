import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_592_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- The wires after evaluating the gates `gs`, starting from `w`.
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (l1 l2 : List Gate) (w : List Bool) :
    run (l1 ++ l2) w = run l2 (run l1 w) := List.foldl_append

theorem run_cons (g : Gate) (l : List Gate) (w : List Bool) :
    run (g :: l) w = run l (step w g) := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false =
      if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false :=
  List.getD_eq_default _ _ h

theorem length_run (l : List Gate) (w : List Bool) :
    (run l w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp [run]
  | cons g l ih => rw [run_cons, ih]; simp [step]; omega

theorem getD_run_of_lt (l : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (run l w).getD i false = w.getD i false := by
  induction l generalizing w with
  | nil => rfl
  | cons g l ih =>
    rw [run_cons, ih _ (by simp [step]; omega), step, getD_snoc, if_pos h]

-- The wires a gate's value actually depends on.
def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ eff g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rcases g with ⟨op, ins⟩
  cases op
  case not =>
    rcases ins with _ | ⟨a, t⟩
    · rfl
    · simp [GateOp.eval, h a (by simp [eff])]
  all_goals exact congrArg _ (List.map_congr_left (fun i hi => h i (by simpa [eff] using hi)))

-- The gate `g` with its input wires renamed by `φ`.
def mapG (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

theorem step_mapG (φ : ℕ → ℕ) (E : Set ℕ) (g : Gate) (W W' : List Bool)
    (hg : ∀ i ∈ eff g, i ∉ E) (hinv : ∀ i, i ∉ E → W'.getD (φ i) false = W.getD i false) :
    step W' (mapG φ g) = W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := by
  simp only [step, mapG, List.map_map]
  rw [eval_congr g ((fun i => W'.getD i false) ∘ φ) (fun i => W.getD i false)
    (fun i hi => hinv i (hg i hi))]

-- The renaming lemma: run the gates `l` from `W`, and their renamed copies from `W'`.
theorem seg (φ : ℕ → ℕ) (E : Set ℕ) : ∀ (l : List Gate) (W W' : List Bool),
    (∀ g ∈ l, ∀ i ∈ eff g, i ∉ E) →
    (∀ i, W.length ≤ i → φ i + W.length = i + W'.length) →
    (∀ i, i < W.length → φ i < W'.length ∨ W'.length + l.length ≤ φ i) →
    (∀ i, i ∉ E → W'.getD (φ i) false = W.getD i false) →
    ∀ i, i ∉ E → (run (l.map (mapG φ)) W').getD (φ i) false = (run l W).getD i false := by
  intro l
  induction l with
  | nil => intro W W' _ _ _ hinv; simpa [run] using hinv
  | cons g l ih =>
    intro W W' hE hoff hrng hinv
    rw [List.map_cons, run_cons, run_cons, step_mapG φ E g W W' (hE g (by simp)) hinv]
    set v := g.op.eval (g.inputs.map fun i => W.getD i false)
    have hstep : step W g = W ++ [v] := rfl
    rw [hstep]
    apply ih
    · exact fun g' hg' => hE g' (by simp [hg'])
    · intro i hi
      simp at hi ⊢
      have := hoff i (by omega)
      omega
    · intro i hi
      simp at hi ⊢
      by_cases h : i < W.length
      · rcases hrng i h with h' | h'
        · left; omega
        · right; simp at h'; omega
      · have := hoff i (by omega)
        left; omega
    · intro i hiE
      rw [getD_snoc, getD_snoc]
      by_cases h : i < W.length
      · rw [if_pos h]
        rcases hrng i h with h' | h'
        · rw [if_pos h', hinv i hiE]
        · simp at h'
          rw [if_neg (by omega), if_neg (by omega), ← hinv i hiE, getD_ge _ _ (by omega)]
      · rw [if_neg h]
        have := hoff i (by omega)
        by_cases h2 : i = W.length
        · rw [if_neg (by omega), if_pos (by omega), if_pos h2]
        · rw [if_neg (by omega), if_neg (by omega), if_neg h2]

-- Setting input wire u to the value of a new NOT gate on wire v.

lemma getD_set_same {α : Type*} (l : List α) (i : ℕ) (a d : α)
    (hi : i < l.length) : (l.set i a).getD i d = a := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma getD_set_other {α : Type*} (l : List α) (i j : ℕ) (a d : α)
    (hij : i ≠ j) : (l.set i a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

theorem ofFn_update {n : ℕ} (x : Fin n → Bool) (i : Fin n) (v : Bool) :
    List.ofFn (Function.update x i v) = (List.ofFn x).set i v := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply]
  by_cases hij : (i : ℕ) = j
  · have : (⟨j, by simpa using h1⟩ : Fin n) = i := Fin.ext hij.symm
    simp [this, hij]
  · have : (⟨j, by simpa using h1⟩ : Fin n) ≠ i := fun h => hij (by rw [← h])
    simp [this, hij]

-- The circuit with one new NOT gate reading wire v, whose output takes the place
-- of input wire u.

def fwd (n u v : ℕ) (C : Circuit) : Circuit :=
  let ψ : ℕ → ℕ := fun i => if i = u then n else if n ≤ i then i + 1 else i
  ⟨⟨GateOp.not, [v]⟩ :: C.gates.map (mapG ψ), ψ C.output⟩

theorem fwd_eval (n u v : ℕ) (C : Circuit) (y : List Bool) (hy : y.length = n) (hu : u < n) :
    (fwd n u v C).eval y = C.eval (y.set u (!(y.getD v false))) := by
  set ψ : ℕ → ℕ := fun i => if i = u then n else if n ≤ i then i + 1 else i with hψ
  set c : Bool := !(y.getD v false) with hc
  have hs : step y ⟨GateOp.not, [v]⟩ = y ++ [c] := by
    simp [step, GateOp.eval, hc]
  rw [Circuit.eval, Circuit.eval, wires_eq, wires_eq]
  simp only [fwd]
  rw [run_cons, hs]
  apply seg ψ ∅ C.gates (y.set u c) (y ++ [c]) (by simp)
  · intro i hi
    simp at hi ⊢
    simp only [hψ]
    split_ifs <;> omega
  · intro i hi
    simp at hi ⊢
    simp only [hψ]
    split_ifs <;> omega
  · intro i _
    simp only [hψ]
    split_ifs with h1 h2
    · rw [h1, getD_snoc, if_neg (by omega), if_pos (by omega),
        getD_set_same y u c false (by omega)]
    · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
    · rw [getD_snoc, if_pos (by omega),
        getD_set_other y u i c false (fun h => h1 h.symm)]
  · simp

end PEqualNP.Outside.L_meta_592_aux

open PEqualNP.Outside.L_meta_592_aux in
theorem PEqualNP.Outside.L_meta_592 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), PEqualNP.MetaComplexity.HasCircuitSize n F s → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => F (Function.update x u (!(x v)))) (s + 1) := by
  intro n s F u v h
  obtain ⟨C, hfan, hsize, heval⟩ := h
  refine ⟨fwd n u.val v.val C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [fwd, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, h0, rfl⟩
    · exact ⟨by simp, by simp⟩
    · have hf := hfan g0 h0
      exact ⟨by simpa [mapG] using hf.1, by simpa [mapG] using hf.2⟩
  · have hsz : C.gates.length ≤ s := hsize
    show (fwd n u.val v.val C).gates.length ≤ s + 1
    simp only [fwd]
    simp only [List.length_cons, List.length_map]
    omega
  · intro x
    have hy : (List.ofFn x).length = n := by simp
    rw [fwd_eval n u.val v.val C (List.ofFn x) hy u.isLt]
    have hv : (List.ofFn x).getD v.val false = x v := by
      simpa using getD_ofFn x v.val v.isLt
    rw [hv, ← ofFn_update]
    exact heval (Function.update x u (!(x v)))
