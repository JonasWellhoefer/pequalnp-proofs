import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2693

-- The graph has the triangles 1-4-8 and 3-6-7 and the five-cycle 0-9-5-2-10, so every vertex
-- cover has at least seven vertices; here this is checked over all vertex sets.
set_option maxRecDepth 100000 in
lemma cover7 : ∀ T : Finset (Fin 11),
    ((0 ∈ T ∨ 9 ∈ T) ∧ (0 ∈ T ∨ 10 ∈ T) ∧ (1 ∈ T ∨ 4 ∈ T) ∧ (1 ∈ T ∨ 8 ∈ T) ∧ (2 ∈ T ∨ 5 ∈ T) ∧ (2 ∈ T ∨ 10 ∈ T) ∧ (3 ∈ T ∨ 6 ∈ T) ∧ (3 ∈ T ∨ 7 ∈ T) ∧ (4 ∈ T ∨ 8 ∈ T) ∧ (4 ∈ T ∨ 10 ∈ T) ∧ (5 ∈ T ∨ 8 ∈ T) ∧ (5 ∈ T ∨ 9 ∈ T) ∧ (6 ∈ T ∨ 7 ∈ T) ∧ (6 ∈ T ∨ 10 ∈ T) ∧ (7 ∈ T ∨ 9 ∈ T) ∧ (8 ∈ T ∨ 9 ∈ T)) → 7 ≤ T.card := by
  decide +kernel

-- A cover of the graph without the edges in U, together with one end of each edge in U,
-- covers the whole graph.
lemma main (U : Finset (Sym2 (Fin 11))) (S : Finset (Fin 11))
    (h : ((PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]).deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (S : Set (Fin 11))) :
    7 ≤ S.card + U.card := by
  classical
  let T : Finset (Fin 11) := S ∪ U.image (fun e => (Quot.out e).1)
  have hT : ∀ a b : Fin 11, (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]).Adj a b → a ∈ T ∨ b ∈ T := by
    intro a b hab
    by_cases he : s(a, b) ∈ U
    · have hm : (Quot.out (s(a, b))).1 ∈ s(a, b) := Sym2.out_fst_mem _
      have himg : (Quot.out (s(a, b))).1 ∈ U.image (fun e => (Quot.out e).1) :=
        Finset.mem_image_of_mem _ he
      rcases Sym2.mem_iff.mp hm with h1 | h1
      · left
        rw [← h1]
        exact Finset.mem_union_right _ himg
      · right
        rw [← h1]
        exact Finset.mem_union_right _ himg
    · have hadj : ((PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]).deleteEdges (U : Set (Sym2 (Fin 11)))).Adj a b := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hab, by simpa using he⟩
      rcases h hadj with h1 | h1
      · left
        exact Finset.mem_union_left _ (by simpa using h1)
      · right
        exact Finset.mem_union_left _ (by simpa using h1)
  have h7 := cover7 T ⟨hT 0 9 (by decide), hT 0 10 (by decide), hT 1 4 (by decide), hT 1 8 (by decide), hT 2 5 (by decide), hT 2 10 (by decide), hT 3 6 (by decide), hT 3 7 (by decide), hT 4 8 (by decide), hT 4 10 (by decide), hT 5 8 (by decide), hT 5 9 (by decide), hT 6 7 (by decide), hT 6 10 (by decide), hT 7 9 (by decide), hT 8 9 (by decide)⟩
  have hc : T.card ≤ S.card + U.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  omega

end PEqualNP.Outside.L_meta_2693

theorem PEqualNP.Outside.L_meta_2693 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card := by
  intro x1 U S h
  exact PEqualNP.Outside.L_meta_2693.main U S h
