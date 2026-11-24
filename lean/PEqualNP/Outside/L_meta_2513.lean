import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2513

open PEqualNP.CircuitLowerBounds

-- Constant propagation. Inputs 4 and 9 are pinned to false. Every wire of the old circuit
-- becomes either a constant or a wire of a new circuit on the eight free inputs. A gate that
-- turns out constant, or a copy of an earlier wire, is not written to the new circuit. Every
-- gate that reads a pinned input is such a gate, so two readers save two gates.

-- One evaluation step of a circuit: append the value of the next gate.
def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma getD_snoc_len (l : List Bool) (b : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [b]).getD n false = b := by
  subst h; simp

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma fold_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    (gs ++ [g]).foldl stepW w = stepW (gs.foldl stepW w) g := by
  simp [List.foldl_append]

-- The value of a symbolic wire: a constant, or a wire of the new circuit.
def interp (W : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

-- The new wires among a list of symbolic wires.
def refs (vs : List (Bool ⊕ ℕ)) : List ℕ := vs.filterMap Sum.getRight?

-- The symbolic wires a gate reads.
def vals (σ : List (Bool ⊕ ℕ)) (g : Gate) : List (Bool ⊕ ℕ) :=
  g.inputs.map fun i => σ.getD i (Sum.inl false)

def notOut (σ : List (Bool ⊕ ℕ)) (gs : List Gate) : Bool ⊕ ℕ → List (Bool ⊕ ℕ) × List Gate
  | Sum.inl b => (σ ++ [Sum.inl (!b)], gs)
  | Sum.inr k => (σ ++ [Sum.inr (8 + gs.length)], gs ++ [⟨GateOp.not, [k]⟩])

def emit (op : GateOp) (c : Bool) (σ : List (Bool ⊕ ℕ)) (gs : List Gate) :
    List ℕ → List (Bool ⊕ ℕ) × List Gate
  | [] => (σ ++ [Sum.inl c], gs)
  | [k] => (σ ++ [Sum.inr k], gs)
  | k :: k' :: t => (σ ++ [Sum.inr (8 + gs.length)], gs ++ [⟨op, k :: k' :: t⟩])

-- One step of constant propagation: the state is the symbolic value of every old wire and
-- the gates of the new circuit so far.
def simpStep (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  match g.op with
  | GateOp.not => notOut st.1 st.2 ((vals st.1 g).headD (Sum.inl false))
  | GateOp.and =>
    if Sum.inl false ∈ vals st.1 g then (st.1 ++ [Sum.inl false], st.2)
    else emit GateOp.and true st.1 st.2 (refs (vals st.1 g))
  | GateOp.or =>
    if Sum.inl true ∈ vals st.1 g then (st.1 ++ [Sum.inl true], st.2)
    else emit GateOp.or false st.1 st.2 (refs (vals st.1 g))
  | _ => (st.1 ++ [Sum.inl false], st.2)

lemma simpStep_and (st : List (Bool ⊕ ℕ) × List Gate) (ins : List ℕ) :
    simpStep st ⟨GateOp.and, ins⟩ =
      if Sum.inl false ∈ vals st.1 ⟨GateOp.and, ins⟩ then (st.1 ++ [Sum.inl false], st.2)
      else emit GateOp.and true st.1 st.2 (refs (vals st.1 ⟨GateOp.and, ins⟩)) := rfl

lemma simpStep_or (st : List (Bool ⊕ ℕ) × List Gate) (ins : List ℕ) :
    simpStep st ⟨GateOp.or, ins⟩ =
      if Sum.inl true ∈ vals st.1 ⟨GateOp.or, ins⟩ then (st.1 ++ [Sum.inl true], st.2)
      else emit GateOp.or false st.1 st.2 (refs (vals st.1 ⟨GateOp.or, ins⟩)) := rfl

lemma simpStep_not (st : List (Bool ⊕ ℕ) × List Gate) (ins : List ℕ) :
    simpStep st ⟨GateOp.not, ins⟩ =
      notOut st.1 st.2 ((vals st.1 ⟨GateOp.not, ins⟩).headD (Sum.inl false)) := rfl

-- The invariant: the old wires are the symbolic wires read in the new circuit, and every
-- reference points to an existing new wire.
def Inv (y : List Bool) (σ : List (Bool ⊕ ℕ)) (gs : List Gate) (wC : List Bool) : Prop :=
  wC = σ.map (interp (gs.foldl stepW y)) ∧ ∀ k, Sum.inr k ∈ σ → k < 8 + gs.length

lemma interp_append (W : List Bool) (b : Bool) (v : Bool ⊕ ℕ)
    (h : ∀ k, v = Sum.inr k → k < W.length) : interp (W ++ [b]) v = interp W v := by
  cases v with
  | inl c => rfl
  | inr k =>
    have hk := h k rfl
    show (W ++ [b]).getD k false = W.getD k false
    rw [List.getD_append _ _ _ _ hk]

lemma inv_keep (y : List Bool) (σ : List (Bool ⊕ ℕ)) (gs : List Gate) (wC : List Bool)
    (v : Bool ⊕ ℕ) (b : Bool) (h : Inv y σ gs wC)
    (hb : b = interp (gs.foldl stepW y) v) (hv : ∀ k, v = Sum.inr k → k < 8 + gs.length) :
    Inv y (σ ++ [v]) gs (wC ++ [b]) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [List.map_append, ← h1, hb]
    rfl
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact h2 k hk
    · exact hv k (List.mem_singleton.mp hk).symm

lemma inv_emit (y : List Bool) (hy : y.length = 8) (σ : List (Bool ⊕ ℕ)) (gs : List Gate)
    (wC : List Bool) (g' : Gate) (b : Bool) (h : Inv y σ gs wC)
    (hb : b = g'.op.eval (g'.inputs.map fun i => (gs.foldl stepW y).getD i false)) :
    Inv y (σ ++ [Sum.inr (8 + gs.length)]) (gs ++ [g']) (wC ++ [b]) := by
  obtain ⟨h1, h2⟩ := h
  have hlen : (gs.foldl stepW y).length = 8 + gs.length := by rw [fold_len, hy]
  have hW : (gs ++ [g']).foldl stepW y = gs.foldl stepW y ++ [b] := by
    rw [fold_snoc, hb]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hW, List.map_append, h1]
    congr 1
    · apply List.map_congr_left
      intro v hv
      exact (interp_append _ _ _ (fun k hk => by rw [hlen]; exact h2 k (hk ▸ hv))).symm
    · show [b] = [(gs.foldl stepW y ++ [b]).getD (8 + gs.length) false]
      rw [getD_snoc_len _ _ _ hlen.symm]
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have := h2 k hk
      simp only [List.length_append, List.length_singleton]
      omega
    · have := Sum.inr.inj (List.mem_singleton.mp hk)
      simp only [List.length_append, List.length_singleton]
      omega

lemma getD_map_interp (W : List Bool) : ∀ (σ : List (Bool ⊕ ℕ)) (i : ℕ),
    (σ.map (interp W)).getD i false = interp W (σ.getD i (Sum.inl false))
  | [], i => by simp [interp]
  | v :: σ, 0 => by simp
  | v :: σ, i + 1 => by simpa using getD_map_interp W σ i

lemma bools_eq (W : List Bool) (σ : List (Bool ⊕ ℕ)) (g : Gate) :
    (g.inputs.map fun i => (σ.map (interp W)).getD i false) = (vals σ g).map (interp W) := by
  simp only [vals, List.map_map]
  apply List.map_congr_left
  intro i _
  exact getD_map_interp W σ i

lemma headD_map_interp (W : List Bool) (vs : List (Bool ⊕ ℕ)) :
    (vs.map (interp W)).headD false = interp W (vs.headD (Sum.inl false)) := by
  cases vs <;> rfl

lemma all_map_true {α : Type} (l : List α) (f : α → Bool) :
    ((l.map f).all id = true) ↔ ∀ a ∈ l, f a = true := by
  simp [List.all_eq_true]

lemma any_map_true {α : Type} (l : List α) (f : α → Bool) :
    ((l.map f).any id = true) ↔ ∃ a ∈ l, f a = true := by
  simp [List.any_eq_true]

lemma mem_refs (vs : List (Bool ⊕ ℕ)) (k : ℕ) : k ∈ refs vs ↔ Sum.inr k ∈ vs := by
  simp [refs, List.mem_filterMap, Sum.getRight?_eq_some_iff]

lemma refs_length_le (vs : List (Bool ⊕ ℕ)) : (refs vs).length ≤ vs.length :=
  List.length_filterMap_le _ _

lemma refs_length_lt : ∀ (vs : List (Bool ⊕ ℕ)) (b : Bool), Sum.inl b ∈ vs →
    (refs vs).length < vs.length
  | [], b, h => by simp at h
  | v :: vs, b, h => by
    rcases List.mem_cons.mp h with h' | h'
    · subst h'
      have hle := refs_length_le vs
      have e : refs (Sum.inl b :: vs) = refs vs := rfl
      rw [e, List.length_cons]
      omega
    · have hlt := refs_length_lt vs b h'
      cases v with
      | inl c =>
        have e : refs (Sum.inl c :: vs) = refs vs := rfl
        rw [e, List.length_cons]
        omega
      | inr k =>
        have e : refs (Sum.inr k :: vs) = k :: refs vs := rfl
        rw [e, List.length_cons, List.length_cons]
        omega

lemma and_val (W : List Bool) (vs : List (Bool ⊕ ℕ)) (hf : Sum.inl false ∉ vs) :
    GateOp.and.eval (vs.map (interp W)) =
      GateOp.and.eval ((refs vs).map fun k => W.getD k false) := by
  apply Bool.eq_iff_iff.mpr
  show ((vs.map (interp W)).all id = true) ↔
    (((refs vs).map fun k => W.getD k false).all id = true)
  rw [all_map_true, all_map_true]
  constructor
  · intro h k hk
    exact h (Sum.inr k) ((mem_refs vs k).mp hk)
  · intro h v hv
    cases v with
    | inl b =>
      cases b with
      | false => exact absurd hv hf
      | true => rfl
    | inr k => exact h k ((mem_refs vs k).mpr hv)

lemma or_val (W : List Bool) (vs : List (Bool ⊕ ℕ)) (hf : Sum.inl true ∉ vs) :
    GateOp.or.eval (vs.map (interp W)) =
      GateOp.or.eval ((refs vs).map fun k => W.getD k false) := by
  apply Bool.eq_iff_iff.mpr
  show ((vs.map (interp W)).any id = true) ↔
    (((refs vs).map fun k => W.getD k false).any id = true)
  rw [any_map_true, any_map_true]
  constructor
  · rintro ⟨v, hv, hval⟩
    cases v with
    | inl b =>
      cases b with
      | false => exact absurd hval (by simp [interp])
      | true => exact absurd hv hf
    | inr k => exact ⟨k, (mem_refs vs k).mpr hv, hval⟩
  · rintro ⟨k, hk, hval⟩
    exact ⟨Sum.inr k, (mem_refs vs k).mp hk, hval⟩

lemma and_false_of_mem (W : List Bool) (vs : List (Bool ⊕ ℕ)) (h : Sum.inl false ∈ vs) :
    GateOp.and.eval (vs.map (interp W)) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have := (all_map_true vs (interp W)).mp ht (Sum.inl false) h
  exact Bool.noConfusion this

lemma or_true_of_mem (W : List Bool) (vs : List (Bool ⊕ ℕ)) (h : Sum.inl true ∈ vs) :
    GateOp.or.eval (vs.map (interp W)) = true :=
  (any_map_true vs (interp W)).mpr ⟨Sum.inl true, h, rfl⟩

lemma vals_mem (σ : List (Bool ⊕ ℕ)) (g : Gate) (k : ℕ) (h : Sum.inr k ∈ vals σ g) :
    Sum.inr k ∈ σ := by
  obtain ⟨i, _, hi⟩ := List.mem_map.mp h
  by_cases hlt : i < σ.length
  · rw [List.getD_eq_getElem _ _ hlt] at hi
    rw [← hi]
    exact List.getElem_mem hlt
  · rw [List.getD_eq_default _ _ (by omega)] at hi
    cases hi

lemma inv_step (y : List Bool) (hy : y.length = 8) (st : List (Bool ⊕ ℕ) × List Gate)
    (wC : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (h : Inv y st.1 st.2 wC) :
    Inv y (simpStep st g).1 (simpStep st g).2 (stepW wC g) := by
  obtain ⟨σ, gs⟩ := st
  dsimp only at h
  have h2 := h.2
  have hb : stepW wC g =
      wC ++ [g.op.eval ((vals σ g).map (interp (gs.foldl stepW y)))] := by
    have e : (g.inputs.map fun i => wC.getD i false) =
        (vals σ g).map (interp (gs.foldl stepW y)) := by
      rw [← bools_eq, ← h.1]
    show wC ++ [g.op.eval (g.inputs.map fun i => wC.getD i false)] = _
    rw [e]
  rw [hb]
  have hsub := vals_mem σ g
  rcases g with ⟨op, ins⟩
  dsimp only at hop
  rcases hop with rfl | rfl | rfl
  · rw [simpStep_and]
    dsimp only
    generalize vals σ ⟨GateOp.and, ins⟩ = vs at hsub ⊢
    by_cases hf : Sum.inl false ∈ vs
    · simp only [hf, ↓reduceIte]
      exact inv_keep y σ gs wC (Sum.inl false) _ h (and_false_of_mem _ vs hf)
        (fun k hk => by cases hk)
    · simp only [hf, ↓reduceIte]
      rw [and_val _ vs hf]
      have hmem := mem_refs vs
      generalize refs vs = r at hmem ⊢
      match r, hmem with
      | [], _ => exact inv_keep y σ gs wC (Sum.inl true) _ h rfl (fun k hk => by cases hk)
      | [k], hmem =>
        refine inv_keep y σ gs wC (Sum.inr k) _ h ?_ ?_
        · simp [GateOp.eval, interp]
        · intro k' hk'
          cases hk'
          exact h2 k (hsub k ((hmem k).mp (by simp)))
      | k :: k' :: t, _ =>
        exact inv_emit y hy σ gs wC ⟨GateOp.and, k :: k' :: t⟩ _ h rfl
  · rw [simpStep_or]
    dsimp only
    generalize vals σ ⟨GateOp.or, ins⟩ = vs at hsub ⊢
    by_cases hf : Sum.inl true ∈ vs
    · simp only [hf, ↓reduceIte]
      exact inv_keep y σ gs wC (Sum.inl true) _ h (or_true_of_mem _ vs hf)
        (fun k hk => by cases hk)
    · simp only [hf, ↓reduceIte]
      rw [or_val _ vs hf]
      have hmem := mem_refs vs
      generalize refs vs = r at hmem ⊢
      match r, hmem with
      | [], _ => exact inv_keep y σ gs wC (Sum.inl false) _ h rfl (fun k hk => by cases hk)
      | [k], hmem =>
        refine inv_keep y σ gs wC (Sum.inr k) _ h ?_ ?_
        · simp [GateOp.eval, interp]
        · intro k' hk'
          cases hk'
          exact h2 k (hsub k ((hmem k).mp (by simp)))
      | k :: k' :: t, _ =>
        exact inv_emit y hy σ gs wC ⟨GateOp.or, k :: k' :: t⟩ _ h rfl
  · rw [simpStep_not]
    dsimp only
    generalize vals σ ⟨GateOp.not, ins⟩ = vs at hsub ⊢
    have hval : GateOp.not.eval (vs.map (interp (gs.foldl stepW y))) =
        !(interp (gs.foldl stepW y) (vs.headD (Sum.inl false))) := by
      rw [← headD_map_interp]
      rfl
    rw [hval]
    have hhead : ∀ k, vs.headD (Sum.inl false) = Sum.inr k → Sum.inr k ∈ vs := by
      intro k hk
      cases vs with
      | nil => simp at hk
      | cons v vs' =>
        have hv : v = Sum.inr k := hk
        rw [hv]
        exact List.mem_cons_self
    generalize vs.headD (Sum.inl false) = hd at hhead ⊢
    cases hd with
    | inl b => exact inv_keep y σ gs wC (Sum.inl (!b)) _ h rfl (fun k hk => by cases hk)
    | inr k => exact inv_emit y hy σ gs wC ⟨GateOp.not, [k]⟩ _ h rfl

lemma inv_fold (y : List Bool) (hy : y.length = 8) :
    ∀ (cs : List Gate),
      (∀ g ∈ cs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
      ∀ (st : List (Bool ⊕ ℕ) × List Gate) (wC : List Bool), Inv y st.1 st.2 wC →
        Inv y (cs.foldl simpStep st).1 (cs.foldl simpStep st).2 (cs.foldl stepW wC) := by
  intro cs
  induction cs with
  | nil => intro _ st wC h; exact h
  | cons g cs ih =>
    intro hops st wC h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg')) _ _
      (inv_step y hy st wC g (hops g (by simp)) h)

-- The structural side: what one step does to the two parts of the state.

lemma emit_fst (op : GateOp) (c : Bool) (σ : List (Bool ⊕ ℕ)) (gs : List Gate) :
    ∀ r : List ℕ, ∃ v, (emit op c σ gs r).1 = σ ++ [v]
  | [] => ⟨_, rfl⟩
  | [_] => ⟨_, rfl⟩
  | _ :: _ :: _ => ⟨_, rfl⟩

lemma emit_snd_le (op : GateOp) (c : Bool) (σ : List (Bool ⊕ ℕ)) (gs : List Gate) :
    ∀ r : List ℕ, (emit op c σ gs r).2.length ≤ gs.length + 1
  | [] => by simp [emit]
  | [_] => by simp [emit]
  | _ :: _ :: _ => by simp [emit]

lemma emit_snd_short (op : GateOp) (c : Bool) (σ : List (Bool ⊕ ℕ)) (gs : List Gate) :
    ∀ r : List ℕ, r.length ≤ 1 → (emit op c σ gs r).2 = gs
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by simp at h

lemma emit_fan (op : GateOp) (c : Bool) (σ : List (Bool ⊕ ℕ)) (gs : List Gate)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) :
    ∀ r : List ℕ, r.length ≤ 2 → ∀ g' ∈ (emit op c σ gs r).2,
      g' ∈ gs ∨ ((g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2)
  | [], _, _, hg' => Or.inl hg'
  | [_], _, _, hg' => Or.inl hg'
  | k :: k' :: t, hr, g', hg' => by
    have hg'' : g' ∈ gs ++ [⟨op, k :: k' :: t⟩] := hg'
    rcases List.mem_append.mp hg'' with h | h
    · exact Or.inl h
    · rw [List.mem_singleton.mp h]
      exact Or.inr ⟨hop, hr⟩

lemma notOut_fst (σ : List (Bool ⊕ ℕ)) (gs : List Gate) :
    ∀ v : Bool ⊕ ℕ, ∃ u, (notOut σ gs v).1 = σ ++ [u]
  | Sum.inl _ => ⟨_, rfl⟩
  | Sum.inr _ => ⟨_, rfl⟩

lemma notOut_snd_le (σ : List (Bool ⊕ ℕ)) (gs : List Gate) :
    ∀ v : Bool ⊕ ℕ, (notOut σ gs v).2.length ≤ gs.length + 1
  | Sum.inl _ => by simp [notOut]
  | Sum.inr _ => by simp [notOut]

lemma notOut_fan (σ : List (Bool ⊕ ℕ)) (gs : List Gate) :
    ∀ v : Bool ⊕ ℕ, ∀ g' ∈ (notOut σ gs v).2,
      g' ∈ gs ∨ ((g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2)
  | Sum.inl _, _, hg' => Or.inl hg'
  | Sum.inr k, g', hg' => by
    have hg'' : g' ∈ gs ++ [⟨GateOp.not, [k]⟩] := hg'
    rcases List.mem_append.mp hg'' with h | h
    · exact Or.inl h
    · rw [List.mem_singleton.mp h]
      exact Or.inr ⟨Or.inr (Or.inr rfl), by simp⟩

lemma step_fst (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∃ v, (simpStep st g).1 = st.1 ++ [v] := by
  rcases g with ⟨op, ins⟩
  dsimp only at hop
  rcases hop with rfl | rfl | rfl
  · rw [simpStep_and]
    split
    · exact ⟨_, rfl⟩
    · exact emit_fst _ _ _ _ _
  · rw [simpStep_or]
    split
    · exact ⟨_, rfl⟩
    · exact emit_fst _ _ _ _ _
  · rw [simpStep_not]
    exact notOut_fst _ _ _

lemma step_snd_le (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (simpStep st g).2.length ≤ st.2.length + 1 := by
  rcases g with ⟨op, ins⟩
  dsimp only at hop
  rcases hop with rfl | rfl | rfl
  · rw [simpStep_and]
    split
    · simp
    · exact emit_snd_le _ _ _ _ _
  · rw [simpStep_or]
    split
    · simp
    · exact emit_snd_le _ _ _ _ _
  · rw [simpStep_not]
    exact notOut_snd_le _ _ _

lemma step_fan (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) :
    ∀ g' ∈ (simpStep st g).2,
      g' ∈ st.2 ∨ ((g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2) := by
  rcases g with ⟨op, ins⟩
  dsimp only at hop hlen
  have hr : ∀ o : GateOp, (refs (vals st.1 ⟨o, ins⟩)).length ≤ 2 := by
    intro o
    refine le_trans (refs_length_le _) ?_
    simpa [vals] using hlen
  rcases hop with rfl | rfl | rfl
  · rw [simpStep_and]
    split
    · intro g' hg'
      exact Or.inl hg'
    · exact emit_fan _ _ _ _ (Or.inl rfl) _ (hr _)
  · rw [simpStep_or]
    split
    · intro g' hg'
      exact Or.inl hg'
    · exact emit_fan _ _ _ _ (Or.inr (Or.inl rfl)) _ (hr _)
  · rw [simpStep_not]
    exact notOut_fan _ _ _

-- The start: the eight free inputs are new wires, the two pinned inputs are the constant false.
def sigma0 : List (Bool ⊕ ℕ) :=
  [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false, Sum.inr 4, Sum.inr 5, Sum.inr 6,
    Sum.inr 7, Sum.inl false]

lemma pre_getD (σ : List (Bool ⊕ ℕ)) (h : sigma0 <+: σ) (i : ℕ) (hi : i = 4 ∨ i = 9) :
    σ.getD i (Sum.inl false) = Sum.inl false := by
  obtain ⟨t, rfl⟩ := h
  rcases hi with rfl | rfl <;> simp [sigma0]

-- The gates the statement counts: those reading input 4 or input 9.
def rd (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any
    fun i => i == 4 || i == 9

lemma step_rd (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hpre : sigma0 <+: st.1) (hrd : rd g = true) :
    (simpStep st g).2 = st.2 := by
  rcases g with ⟨op, ins⟩
  dsimp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · have hex : ∃ i ∈ ins, i = 4 ∨ i = 9 := by simpa [rd, GateOp.eval] using hrd
    obtain ⟨i, hi, h49⟩ := hex
    have hmem : Sum.inl false ∈ vals st.1 ⟨GateOp.and, ins⟩ :=
      List.mem_map.mpr ⟨i, hi, pre_getD st.1 hpre i h49⟩
    rw [simpStep_and]
    simp only [hmem, ↓reduceIte]
  · have hex : ∃ i ∈ ins, i = 4 ∨ i = 9 := by simpa [rd, GateOp.eval] using hrd
    obtain ⟨i, hi, h49⟩ := hex
    have hmem : Sum.inl false ∈ vals st.1 ⟨GateOp.or, ins⟩ :=
      List.mem_map.mpr ⟨i, hi, pre_getD st.1 hpre i h49⟩
    rw [simpStep_or]
    split
    · rfl
    · apply emit_snd_short
      have h1 := refs_length_lt _ false hmem
      have h2 : (vals st.1 ⟨GateOp.or, ins⟩).length = ins.length := by simp [vals]
      omega
  · cases ins with
    | nil => simp [rd, GateOp.eval] at hrd
    | cons i rest =>
      have h49 : i = 4 ∨ i = 9 := by simpa [rd, GateOp.eval] using hrd
      have hhead : (vals st.1 ⟨GateOp.not, i :: rest⟩).headD (Sum.inl false) = Sum.inl false :=
        pre_getD st.1 hpre i h49
      rw [simpStep_not, hhead]
      rfl

lemma fold_pre : ∀ (cs : List Gate),
    (∀ g ∈ cs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    ∀ st : List (Bool ⊕ ℕ) × List Gate, sigma0 <+: st.1 → sigma0 <+: (cs.foldl simpStep st).1
  | [], _, _, h => h
  | g :: cs, hops, st, h => by
    rw [List.foldl_cons]
    apply fold_pre cs (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨v, hv⟩ := step_fst st g (hops g (by simp))
    rw [hv]
    exact h.trans (List.prefix_append _ _)

lemma fold_count : ∀ (cs : List Gate),
    (∀ g ∈ cs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ g ∈ cs, g.inputs.length ≤ 2) →
    ∀ st : List (Bool ⊕ ℕ) × List Gate, sigma0 <+: st.1 →
      (cs.foldl simpStep st).2.length + cs.countP rd ≤ st.2.length + cs.length
  | [], _, _, _, _ => by simp
  | g :: cs, hops, hlens, st, h => by
    have hop := hops g (by simp)
    have hlen := hlens g (by simp)
    have hpre : sigma0 <+: (simpStep st g).1 := by
      obtain ⟨v, hv⟩ := step_fst st g hop
      rw [hv]
      exact h.trans (List.prefix_append _ _)
    have ih := fold_count cs (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hlens g' (List.mem_cons_of_mem _ hg')) (simpStep st g) hpre
    have hle := step_snd_le st g hop
    rw [List.foldl_cons, List.length_cons]
    by_cases hrd : rd g = true
    · have heq := step_rd st g hop hlen h hrd
      rw [List.countP_cons_of_pos hrd]
      rw [heq] at ih
      omega
    · rw [List.countP_cons_of_neg hrd]
      omega

lemma fold_fan : ∀ (cs : List Gate),
    (∀ g ∈ cs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ g ∈ cs, g.inputs.length ≤ 2) →
    ∀ (st : List (Bool ⊕ ℕ) × List Gate), ∀ g' ∈ (cs.foldl simpStep st).2,
      g' ∈ st.2 ∨ ((g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2)
  | [], _, _, _, _, hg' => Or.inl hg'
  | g :: cs, hops, hlens, st, g', hg' => by
    rw [List.foldl_cons] at hg'
    rcases fold_fan cs (fun g'' hg'' => hops g'' (List.mem_cons_of_mem _ hg''))
      (fun g'' hg'' => hlens g'' (List.mem_cons_of_mem _ hg'')) (simpStep st g) g' hg' with h | h
    · exact step_fan st g (hops g (by simp)) (hlens g (by simp)) g' h
    · exact Or.inr h

-- The pinned input of the statement.
def emb (y : Fin 8 → Bool) : List Bool :=
  [y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7, false]

lemma ofFn8 (y : Fin 8 → Bool) : List.ofFn y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7] := by
  simp [List.ofFn_succ]

lemma inv_init (y : Fin 8 → Bool) : Inv (List.ofFn y) sigma0 [] (emb y) := by
  refine ⟨?_, ?_⟩
  · show emb y = sigma0.map (interp (List.ofFn y))
    rw [ofFn8]
    rfl
  · intro k hk
    simp [sigma0] at hk
    simp only [List.length_nil]
    omega

lemma main (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hcount : 2 ≤ List.countP rd C.gates)
    (hne : ∃ y z : Fin 8 → Bool, C.eval (emb y) ≠ C.eval (emb z)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = C.eval (emb y) := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => by simpa using (hC g hg).1
  have hlens : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hC g hg).2
  have hinv : ∀ y : Fin 8 → Bool,
      Inv (List.ofFn y) (C.gates.foldl simpStep (sigma0, [])).1
        (C.gates.foldl simpStep (sigma0, [])).2 (C.gates.foldl stepW (emb y)) :=
    fun y => inv_fold (List.ofFn y) (by simp) C.gates hops (sigma0, []) (emb y) (inv_init y)
  have hfan := fold_fan C.gates hops hlens (sigma0, [])
  have hcnt := fold_count C.gates hops hlens (sigma0, []) (List.prefix_refl _)
  obtain ⟨st, hst⟩ : ∃ st, C.gates.foldl simpStep (sigma0, []) = st := ⟨_, rfl⟩
  rw [hst] at hinv hfan hcnt
  have heval : ∀ y : Fin 8 → Bool, C.eval (emb y) =
      interp (st.2.foldl stepW (List.ofFn y)) (st.1.getD C.output (Sum.inl false)) := by
    intro y
    unfold Circuit.eval
    rw [wires_eq, (hinv y).1, getD_map_interp]
  cases hout : st.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨y, z, hyz⟩ := hne
    apply hyz
    rw [heval y, heval z, hout]
    rfl
  | inr k =>
    refine ⟨⟨st.2, k⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases hfan g hg with h | h
      · simp at h
      · exact ⟨by simpa using h.1, h.2⟩
    · have hsz : C.size = C.gates.length := rfl
      show st.2.length + 2 ≤ C.size
      simp only [List.length_nil] at hcnt
      omega
    · intro y
      rw [heval y, hout]
      rfl

end PEqualNP.Outside.L_meta_2513

theorem PEqualNP.Outside.L_meta_2513 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Fin (8 : ℕ) → Bool) => [x2 (0 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), Bool.false, x2 (4 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (6 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), Bool.false]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (2 : ℕ) ≤ List.countP x1 x3.gates → (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x3.eval (x2 x6) ≠ x3.eval (x2 x7)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size + (2 : ℕ) ≤ x3.size ∧ ∀ (x8 : Fin (8 : ℕ) → Bool), x7.eval (List.ofFn x8) = x3.eval (x2 x8) := by
  intro x1 x2 C hC hcount hne
  exact PEqualNP.Outside.L_meta_2513.main C hC hcount hne
