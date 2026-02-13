

theorem P2_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  -- Decompose the membership of `x`
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∉ B := hx.2
  -- `P2 A` gives the following interior membership
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- Define an auxiliary open neighbourhood of `x`
  let S : Set X := interior (closure (interior A)) ∩ Bᶜ
  have hS_open : IsOpen S := by
    dsimp [S]
    exact IsOpen.inter isOpen_interior hB.isOpen_compl
  have hxS : x ∈ S := by
    dsimp [S] at *
    exact And.intro hx_int hx_notB
  -- Show that `S ⊆ closure (interior (A \ B))`
  have hS_subset : (S) ⊆ closure (interior (A \ B)) := by
    intro y hy
    dsimp [S] at hy
    -- Split the conditions on `y`
    have hy_int : y ∈ interior (closure (interior A)) := hy.1
    have hy_notB : y ∉ B := hy.2
    -- From the first, we also get `y ∈ closure (interior A)`
    have hy_cl : y ∈ closure (interior A) := interior_subset hy_int
    -- Prove `y ∈ closure (interior (A \ B))`
    apply (mem_closure_iff).2
    intro V hV hyV
    -- Intersect the neighbourhood with `Bᶜ`
    have hW_open : IsOpen (V ∩ Bᶜ : Set X) :=
      IsOpen.inter hV hB.isOpen_compl
    have hyW : y ∈ V ∩ Bᶜ := And.intro hyV hy_notB
    -- Since `y ∈ closure (interior A)`, this intersection meets `interior A`
    have h_nonempty : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
      have h_mem := (mem_closure_iff).1 hy_cl
      have h := h_mem (V ∩ Bᶜ) hW_open hyW
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using h
    rcases h_nonempty with ⟨z, hz⟩
    -- Break down the membership of `z`
    have hzV : z ∈ V := (hz.1).1
    have hz_notB : z ∉ B := (hz.1).2
    have hz_intA : z ∈ interior A := hz.2
    -- Build an open subset of `A \ B` containing `z`
    have hT_open : IsOpen (interior A ∩ Bᶜ : Set X) :=
      IsOpen.inter isOpen_interior hB.isOpen_compl
    have hT_sub : (interior A ∩ Bᶜ : Set X) ⊆ (A \ B) := by
      intro w hw
      exact And.intro (interior_subset hw.1) hw.2
    have hz_interior_diff : z ∈ interior (A \ B) := by
      have hzT : z ∈ interior A ∩ Bᶜ := And.intro hz_intA hz_notB
      have := interior_maximal hT_sub hT_open
      exact this hzT
    -- Provide the desired witness in `V ∩ interior (A \ B)`
    exact ⟨z, And.intro hzV hz_interior_diff⟩
  -- Upgrade the inclusion using maximality of the interior
  have hS_subset_int : (S) ⊆ interior (closure (interior (A \ B))) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`
  have hx_final : x ∈ interior (closure (interior (A \ B))) :=
    hS_subset_int hxS
  simpa using hx_final

theorem P3_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  -- Decompose the membership of `x`
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∉ B := hx.2
  -- `P3 A` gives an interior membership
  have hx_int : x ∈ interior (closure A) := hA hxA
  -- Define an auxiliary open neighbourhood
  let S : Set X := interior (closure A) ∩ Bᶜ
  have hS_open : IsOpen S := by
    dsimp [S]
    exact IsOpen.inter isOpen_interior hB.isOpen_compl
  have hxS : x ∈ S := by
    dsimp [S]
    exact And.intro hx_int hx_notB
  -- Show that `S ⊆ closure (A \ B)`
  have hS_subset : (S : Set X) ⊆ closure (A \ B) := by
    intro y hy
    dsimp [S] at hy
    have hy_int : y ∈ interior (closure A) := hy.1
    have hy_notB : y ∉ B := hy.2
    have hy_cl : y ∈ closure A := interior_subset hy_int
    -- Prove `y ∈ closure (A \ B)` using neighbourhoods
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro V hV hyV
      -- Refine the neighbourhood to avoid `B`
      have hW_open : IsOpen (V ∩ Bᶜ) := IsOpen.inter hV hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := And.intro hyV hy_notB
      -- Because `y ∈ closure A`, this intersection meets `A`
      have h_nonempty : ((V ∩ Bᶜ) ∩ A).Nonempty := by
        have h_mem := (mem_closure_iff).1 hy_cl
        have h := h_mem (V ∩ Bᶜ) hW_open hyW
        simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using h
      rcases h_nonempty with ⟨z, hz⟩
      -- Extract the desired witness in `V ∩ (A \ B)`
      have hzV : z ∈ V := (hz.1).1
      have hz_notB : z ∉ B := (hz.1).2
      have hzA : z ∈ A := hz.2
      exact
        ⟨z, And.intro hzV (And.intro hzA hz_notB)⟩
    exact this
  -- Upgrade the inclusion via maximality of the interior
  have hS_subset_int : (S : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`
  exact hS_subset_int hxS

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (Set.prod (Set.prod A B) C) := by
  have hAB : Topology.P2 (Set.prod A B) := Topology.P2_prod hA hB
  simpa using Topology.P2_prod hAB hC

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (Set.prod (Set.prod A B) C) := by
  have hAB : Topology.P3 (Set.prod A B) := Topology.P3_prod hA hB
  simpa using Topology.P3_prod hAB hC

theorem P2_iff_P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 A ↔ Topology.P1 A := by
  simpa [Topology.P1_iff_P3_of_dense_interior (X := X) (A := A) h]
    using (Topology.P2_iff_P1_and_P3 (X := X) (A := A))

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro _hP2
    exact Topology.P3_of_open (A := A) hA
  · intro _hP3
    exact Topology.P2_of_open (A := A) hA