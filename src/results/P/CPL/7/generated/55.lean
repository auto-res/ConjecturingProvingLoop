

theorem P1_restrict {X : Type*} [TopologicalSpace X] {A : Set X} {U : Set X} (hU : IsOpen U) : Topology.P1 A → Topology.P1 (A ∩ U) := by
  intro hP1
  intro x hx
  rcases hx with ⟨hxA, hxU⟩
  -- `x` is in the closure of `interior A`
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Use the neighbourhood criterion for closures
  apply (mem_closure_iff).2
  intro V hV_open hxV
  -- Work inside the open set `V ∩ U`
  have hW_open : IsOpen (V ∩ U) := hV_open.inter hU
  have hxW : x ∈ V ∩ U := And.intro hxV hxU
  -- `V ∩ U` meets `interior A`
  rcases (mem_closure_iff).1 hx_cl (V ∩ U) hW_open hxW with
    ⟨y, hyW, hy_intA⟩
  -- From `y ∈ interior A ∩ U`, deduce `y ∈ interior (A ∩ U)`
  have hy_intAU : y ∈ interior (A ∩ U) := by
    -- `interior A ∩ U` is an open subset of `A ∩ U`
    have h_subset :
        (interior (A : Set X) ∩ U : Set X) ⊆ interior (A ∩ U) := by
      have h_open : IsOpen (interior (A : Set X) ∩ U) :=
        isOpen_interior.inter hU
      have h_basic :
          (interior (A : Set X) ∩ U : Set X) ⊆ A ∩ U := by
        intro z hz
        exact And.intro (interior_subset hz.1) hz.2
      exact interior_maximal h_basic h_open
    have : y ∈ interior (A : Set X) ∩ U := And.intro hy_intA hyW.2
    exact h_subset this
  -- Provide the required witness in `V ∩ interior (A ∩ U)`
  exact ⟨y, And.intro hyW.1 hy_intAU⟩

theorem P1_prod_three {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 (A ×ˢ B ×ˢ C) := by
  intro hA hB hC
  -- First, obtain `P1` for the product `B ×ˢ C`.
  have hBC : Topology.P1 (B ×ˢ C) := P1_prod hB hC
  -- Next, combine this with `A` to get the desired triple product.
  have hABC : Topology.P1 (A ×ˢ (B ×ˢ C)) := P1_prod hA hBC
  simpa using hABC