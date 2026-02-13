

theorem Topology.P1_of_P1_and_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → (A ⊆ B) → (B ⊆ closure (A : Set X)) → Topology.P1 B := by
  intro hP1 hAB hBSub
  intro x hxB
  -- Step 1: move from `B` to `closure A`.
  have hx_clA : (x : X) ∈ closure (A : Set X) := hBSub hxB
  -- Step 2: use `P1 A` to pass to `closure (interior A)`.
  have h_clA_to_clIntA :
      (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  have hx_clIntA : x ∈ closure (interior A) := h_clA_to_clIntA hx_clA
  -- Step 3: enlarge interiors via the inclusion `A ⊆ B`.
  have hIntMono : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have hClMono :
      closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntMono
  -- Step 4: conclude the desired membership.
  exact hClMono hx_clIntA