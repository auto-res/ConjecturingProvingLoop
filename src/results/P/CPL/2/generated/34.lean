

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 (X:=X) A) (hB : Topology.P1 (X:=Y) B) : Topology.P1 (X:=X×Y) (A ×ˢ B) := by
  -- Unfold the definition of `P1`
  unfold Topology.P1 at hA hB ⊢
  -- We prove the required inclusion point-wise
  intro z hz
  -- Extract the component memberships
  have hxA : z.1 ∈ A := hz.1
  have hyB : z.2 ∈ B := hz.2
  -- Apply `P1` for each coordinate
  have hx_cl : z.1 ∈ closure (interior A) := hA hxA
  have hy_cl : z.2 ∈ closure (interior B) := hB hyB
  -- Step 1: `(z.1, z.2)` lies in the closure of `interior A ×ˢ interior B`
  have h_mem_prod : z ∈ closure (interior A ×ˢ interior B) := by
    -- Use `closure_prod_eq`
    have : z ∈ (closure (interior A) ×ˢ closure (interior B)) := ⟨hx_cl, hy_cl⟩
    simpa [closure_prod_eq] using this
  -- Step 2: `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`
  have h_subset_int :
      (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
    -- First, it is contained in `A ×ˢ B`
    have h_subset_AB :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ (A ×ˢ B) := by
      intro p hp
      exact ⟨
        (interior_subset : interior A ⊆ A) hp.1,
        (interior_subset : interior B ⊆ B) hp.2⟩
    -- Next, it is open
    have h_open :
        IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior : IsOpen (interior A)).prod
        (isOpen_interior : IsOpen (interior B))
    -- Conclude by `interior_maximal`
    exact interior_maximal h_subset_AB h_open
  -- Step 3: take closures to obtain the desired inclusion
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) := closure_mono h_subset_int
  -- Step 4: finish
  exact h_closure_subset h_mem_prod

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 (X:=X) A) (hB : Topology.P2 (X:=Y) B) : Topology.P2 (X:=X×Y) (A ×ˢ B) := by
  classical
  -- Unpack the definition of `P2`
  unfold Topology.P2 at hA hB ⊢
  intro z hz
  -- Apply `P2` to each coordinate
  have hx : z.1 ∈ interior (closure (interior A)) := hA hz.1
  have hy : z.2 ∈ interior (closure (interior B)) := hB hz.2
  -- Auxiliary open neighbourhoods in each factor
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  -- Openness of the auxiliary sets
  have hU_open : IsOpen U := by
    simpa [U] using
      (isOpen_interior : IsOpen (interior (closure (interior A))))
  have hV_open : IsOpen V := by
    simpa [V] using
      (isOpen_interior : IsOpen (interior (closure (interior B))))
  -- The point `z` belongs to `U ×ˢ V`
  have hzU : z.1 ∈ U := by
    simpa [U] using hx
  have hzV : z.2 ∈ V := by
    simpa [V] using hy
  have h_mem_UV : z ∈ (U ×ˢ V : Set (X × Y)) := by
    exact ⟨hzU, hzV⟩
  -- `U ×ˢ V` is open
  have hUV_open : IsOpen (U ×ˢ V : Set (X × Y)) := hU_open.prod hV_open
  -- `U ×ˢ V ⊆ closure (interior A ×ˢ interior B)`
  have hU_subset : (U : Set X) ⊆ closure (interior A) := by
    intro x hxU
    -- `interior_subset` furnishes the inclusion
    have : x ∈ interior (closure (interior A)) := by
      simpa [U] using hxU
    exact interior_subset this
  have hV_subset : (V : Set Y) ⊆ closure (interior B) := by
    intro y hyV
    have : y ∈ interior (closure (interior B)) := by
      simpa [V] using hyV
    exact interior_subset this
  have h_subset_prod :
      (U ×ˢ V : Set (X × Y)) ⊆
        (closure (interior A) ×ˢ closure (interior B)) :=
    Set.prod_mono hU_subset hV_subset
  have h_subset :
      (U ×ˢ V : Set (X × Y)) ⊆
        closure (interior A ×ˢ interior B) := by
    simpa [closure_prod_eq] using h_subset_prod
  -- Hence `z` is in the interior of that closure
  have hz_small :
      z ∈ interior (closure (interior A ×ˢ interior B)) :=
    (mem_interior.2 ⟨U ×ˢ V, h_subset, hUV_open, h_mem_UV⟩)
  -- Relate `interior A ×ˢ interior B` with `interior (A ×ˢ B)`
  have h_int_subset :
      (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
    -- First, it is contained in `A ×ˢ B`
    have h_into_AB :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ (A ×ˢ B) := by
      intro p hp
      exact
        ⟨(interior_subset : interior A ⊆ A) hp.1,
         (interior_subset : interior B ⊆ B) hp.2⟩
    -- Openness of the left-hand side
    have h_open :
        IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior : IsOpen (interior A)).prod
        (isOpen_interior : IsOpen (interior B))
    -- Use `interior_maximal`
    exact interior_maximal h_into_AB h_open
  -- Passage to closures and interiors
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_int_subset
  -- Conclude via monotonicity of `interior`
  exact (interior_mono h_closure_subset) hz_small

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 (X:=X) A) (hB : Topology.P3 (X:=Y) B) : Topology.P3 (X:=X×Y) (A ×ˢ B) := by
  classical
  -- unpack the definition of `P3`
  unfold Topology.P3 at hA hB ⊢
  -- take a point in the product set
  intro z hz
  -- coordinates belong to the factors
  have hxA : z.1 ∈ A := hz.1
  have hyB : z.2 ∈ B := hz.2
  -- apply `P3` for each coordinate
  have hxU : z.1 ∈ interior (closure A) := hA hxA
  have hyV : z.2 ∈ interior (closure B) := hB hyB
  -- auxiliary open neighbourhoods
  let U : Set X := interior (closure A)
  let V : Set Y := interior (closure B)
  have hU_open : IsOpen U := by
    simpa [U] using (isOpen_interior : IsOpen (interior (closure A)))
  have hV_open : IsOpen V := by
    simpa [V] using (isOpen_interior : IsOpen (interior (closure B)))
  -- the point lies in `U ×ˢ V`
  have hzUV : z ∈ (U ×ˢ V : Set (X × Y)) := by
    exact ⟨by simpa [U] using hxU, by simpa [V] using hyV⟩
  -- `U ×ˢ V` is contained in the desired closure
  have h_subset : (U ×ˢ V : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    -- first, `U ⊆ closure A` and `V ⊆ closure B`
    have h1 : (U : Set X) ⊆ closure A := by
      intro x hx
      have : x ∈ interior (closure A) := by simpa [U] using hx
      exact interior_subset this
    have h2 : (V : Set Y) ⊆ closure B := by
      intro y hy
      have : y ∈ interior (closure B) := by simpa [V] using hy
      exact interior_subset this
    -- combine the two inclusions
    have h_prod : (U ×ˢ V : Set (X × Y)) ⊆ (closure A ×ˢ closure B) :=
      Set.prod_mono h1 h2
    simpa [closure_prod_eq] using h_prod
  -- conclude that `z` is in the interior of the closure
  exact
    (mem_interior.2
      ⟨U ×ˢ V, h_subset, hU_open.prod hV_open, hzUV⟩)