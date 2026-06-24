

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  intro x hxA
  exact interior_subset (hP2 hxA)

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_closure_subset : closure (interior A) ⊆ closure A := by
    exact closure_mono interior_subset
  have h_interior_subset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact h_interior_subset hx_int

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA
  intro x hxA
  have h_sub : (A : Set X) ⊆ closure (interior A) := by
    intro y hy
    have : y ∈ closure A := subset_closure hy
    simpa [hA.interior_eq] using this
  have : (∃ U : Set X, U ⊆ closure (interior A) ∧ IsOpen U ∧ x ∈ U) := by
    exact ⟨A, h_sub, hA, hxA⟩
  exact mem_interior.2 this

theorem P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P1 A := by
  intro h_dense
  dsimp [P1]
  intro x hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_dense] using hx_univ

theorem P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P2 A := by
  intro h_dense
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_dense] using this

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro h_dense
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_dense] using this

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_cl : x ∈ closure (interior A) := hA hxA
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact h_sub hx_cl
  | inr hxB =>
      -- `x ∈ B`
      have hx_cl : x ∈ closure (interior B) := hB hxB
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact h_sub hx_cl

theorem P2_diff {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → IsClosed B → P2 (A \ B) := by
  intro hP2 hBclosed
  -- Unfold the definition of `P2`
  dsimp [P2] at hP2 ⊢
  intro x hx_diff
  -- Split the facts about `x`
  have hxA    : x ∈ A   := hx_diff.1
  have hx_notB : x ∉ B := hx_diff.2
  -- `x` lies in the given interior thanks to `hP2`
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Choose an open neighbourhood `U` of `x` contained in `closure (interior A)`
  rcases (mem_interior.1 hx_int) with ⟨U, hU_sub, hU_open, hxU⟩
  -- Refine `U` so that it avoids `B`
  let V : Set X := U ∩ Bᶜ
  have hxV : (x : X) ∈ V := by
    dsimp [V]; exact And.intro hxU hx_notB
  have hV_open : IsOpen V := hU_open.inter hBclosed.isOpen_compl
  -- Main claim: every point of `V` is in the desired closure
  have hV_sub : (V : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hyV
    have hyU    : y ∈ U   := hyV.1
    have hy_notB : y ∉ B := hyV.2
    have hy_clA : y ∈ closure (interior A) := hU_sub hyU
    -- Show `y ∈ closure (interior (A \ B))`
    have : y ∈ closure (interior (A \ B)) := by
      -- Use the characterization via neighbourhoods
      apply (mem_closure_iff).2
      intro W hW_open hyW
      -- Work in the open set that also avoids `B`
      have hW'open : IsOpen (W ∩ Bᶜ) := hW_open.inter hBclosed.isOpen_compl
      have hyW'    : y ∈ W ∩ Bᶜ     := And.intro hyW hy_notB
      -- Intersect with `interior A`
      have h_nonempty₁ : ((W ∩ Bᶜ) ∩ interior A).Nonempty := by
        have := (mem_closure_iff).1 hy_clA (W ∩ Bᶜ) hW'open hyW'
        simpa [Set.inter_assoc, Set.inter_comm] using this
      rcases h_nonempty₁ with ⟨z, hzWBC, hz_intA⟩
      rcases hzWBC with ⟨hzW, hz_notB⟩
      -- An open neighbourhood of `z` inside `A`
      rcases (mem_interior.1 hz_intA) with ⟨O₁, hO₁_sub, hO₁_open, hzO₁⟩
      -- Refine it to stay outside `B`
      have hO_open : IsOpen (O₁ ∩ Bᶜ) := hO₁_open.inter hBclosed.isOpen_compl
      have hO_sub  : (O₁ ∩ Bᶜ) ⊆ A \ B := by
        intro t ht
        have htA  : t ∈ A := hO₁_sub ht.1
        exact And.intro htA ht.2
      have hz_in  : z ∈ O₁ ∩ Bᶜ := And.intro hzO₁ hz_notB
      have hz_int_diff : z ∈ interior (A \ B) :=
        (mem_interior.2 ⟨O₁ ∩ Bᶜ, hO_sub, hO_open, hz_in⟩)
      -- Produce the required witness in `W ∩ interior (A \ B)`
      exact ⟨z, And.intro hzW hz_int_diff⟩
    exact this
  -- `V` witnesses that `x` is in the required interior
  have : x ∈ interior (closure (interior (A \ B))) := by
    apply (mem_interior.2)
    exact ⟨V, hV_sub, hV_open, hxV⟩
  exact this