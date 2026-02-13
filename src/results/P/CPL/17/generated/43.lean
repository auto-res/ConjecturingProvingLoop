

theorem P2_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ Topology.P2 U := by
  intro _hP2A
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      P2_interior (X := X) (A := A)⟩

theorem P1_iff_exists_closed_superset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ ∃ C, IsClosed C ∧ A ⊆ C ∧ C ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact ⟨closure (interior A), isClosed_closure, hP1, subset_rfl⟩
  · rintro ⟨C, _hC_closed, hA_sub_C, hC_sub_cl⟩
    exact Set.Subset.trans hA_sub_C hC_sub_cl

theorem P3_dense_open_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Dense A → (Topology.P3 A ↔ IsOpen (closure A)) := by
  intro hDense
  have hIsOpen : IsOpen (closure (A : Set X)) := by
    simpa [hDense.closure_eq] using isOpen_univ
  have hP3 : P3 A := P3_of_dense (X := X) (A := A) hDense
  exact ⟨fun _ => hIsOpen, fun _ => hP3⟩

theorem P2_prod_of_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : IsOpen A → Topology.P2 B → Topology.P2 (A ×ˢ B) := by
  intro hOpen hP2B
  exact P2_prod (A := A) (B := B) (P2_of_open (A := A) hOpen) hP2B

theorem P3_intersection_open {X : Type*} [TopologicalSpace X] {A U : Set X} (hU : IsOpen U) : Topology.P3 A → Topology.P3 (A ∩ U) := by
  intro hP3A
  intro x hx
  rcases hx with ⟨hxA, hxU⟩
  -- `P3` for `A`
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  -- The open set we shall work with
  have hW_open : IsOpen (interior (closure A) ∩ U) :=
    (isOpen_interior : IsOpen (interior (closure A))).inter hU
  have hxW : x ∈ (interior (closure A) ∩ U) := by
    exact ⟨hx_int, hxU⟩
  -- `W ⊆ closure (A ∩ U)`
  have hW_sub : (interior (closure A) ∩ U : Set X) ⊆ closure (A ∩ U) := by
    intro y hy
    have hy_int : y ∈ interior (closure A) := hy.1
    have hyU   : y ∈ U := hy.2
    have hy_clA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hy_int
    -- show that `y ∈ closure (A ∩ U)`
    have : y ∈ closure (A ∩ U) := by
      -- use the neighborhood characterization of closure
      apply (mem_closure_iff).2
      intro V hV_open hyV
      -- work in the open set `V ∩ U`
      have hVU_open : IsOpen (V ∩ U) := hV_open.inter hU
      have hy_VU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- since `y ∈ closure A`, `A` meets `V ∩ U`
      have h_nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ U) hVU_open hy_VU
      rcases h_nonempty with ⟨z, ⟨hzVU, hzA⟩⟩
      rcases hzVU with ⟨hzV, hzU⟩
      -- `z` lies in `V ∩ (A ∩ U)`
      exact ⟨z, ⟨hzV, ⟨hzA, hzU⟩⟩⟩
    exact this
  -- an open subset of a closure lies in its interior
  have hW_sub_int :
      (interior (closure A) ∩ U : Set X) ⊆ interior (closure (A ∩ U)) :=
    interior_maximal hW_sub hW_open
  exact hW_sub_int hxW