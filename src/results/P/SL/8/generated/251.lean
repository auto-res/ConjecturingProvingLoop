

theorem isOpen_P1_inter_imp_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hP1B : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  dsimp [Topology.P1] at hP1B ⊢
  intro x hx
  -- Decompose the membership `x ∈ A ∩ B`.
  have hxA : x ∈ A := hx.1
  have hxB : x ∈ B := hx.2
  -- Apply `P1 B` to obtain `x ∈ closure (interior B)`.
  have hxClB : x ∈ closure (interior B) := hP1B hxB
  -- We first show that `x ∈ closure (A ∩ interior B)`.
  have hxClAIntB : x ∈ closure (A ∩ interior B) := by
    -- Use the neighborhood characterization of the closure.
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Consider the open neighborhood `U ∩ A` of `x`.
    have hUA_open : IsOpen (U ∩ A) := hUopen.inter hA
    have hxUA : x ∈ U ∩ A := And.intro hxU hxA
    -- Since `x ∈ closure (interior B)`, this neighborhood meets `interior B`.
    have hNon : (U ∩ A ∩ interior B).Nonempty :=
      (mem_closure_iff).1 hxClB (U ∩ A) hUA_open hxUA
    -- Rewriting yields the required non‐emptiness.
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hNon
  -- Show that `A ∩ interior B` is contained in `interior (A ∩ B)`.
  have hSubset : A ∩ interior B ⊆ interior (A ∩ B) := by
    intro y hy
    -- The set `A ∩ interior B` is open.
    have hOpen : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    -- It is contained in `A ∩ B`.
    have hSub : A ∩ interior B ⊆ A ∩ B := by
      intro z hz
      exact And.intro hz.1 (interior_subset hz.2)
    -- Hence each of its points lies in the interior of `A ∩ B`.
    exact
      (Set.mem_interior).2 ⟨A ∩ interior B, hOpen, hSub, hy⟩
  -- Monotonicity of the closure yields the desired membership.
  exact (closure_mono hSubset) hxClAIntB