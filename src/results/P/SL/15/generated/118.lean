

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ×ˢ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro p hp
  -- Coordinates of the point `p`.
  have hAx : p.1 ∈ A := hp.1
  have hBy : p.2 ∈ B := hp.2
  -- Apply the `P3` property to each coordinate.
  have hIntA : p.1 ∈ interior (closure A) := hA hAx
  have hIntB : p.2 ∈ interior (closure B) := hB hBy
  -- The product of these interiors is an open neighbourhood of `p`.
  have hOpen :
      IsOpen (Set.prod (interior (closure A)) (interior (closure B))) :=
    (isOpen_interior).prod isOpen_interior
  have hMem :
      (p : X × Y) ∈ Set.prod (interior (closure A)) (interior (closure B)) :=
    ⟨hIntA, hIntB⟩
  -- This neighbourhood is contained in `closure (A ×ˢ B)`.
  have hSub :
      Set.prod (interior (closure A)) (interior (closure B)) ⊆
        closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure A := interior_subset hqA
    have hqB_cl : q.2 ∈ closure B := interior_subset hqB
    have h_eq :
        closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
      simpa using closure_prod_eq
    have : (q : X × Y) ∈ (closure A) ×ˢ (closure B) :=
      ⟨hqA_cl, hqB_cl⟩
    simpa [h_eq] using this
  -- Turn the neighbourhood into an interior membership.
  have h_nhds :
      closure (A ×ˢ B) ∈ 𝓝 p :=
    Filter.mem_of_superset (hOpen.mem_nhds hMem) hSub
  exact (mem_interior_iff_mem_nhds).2 h_nhds