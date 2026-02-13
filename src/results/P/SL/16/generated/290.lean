

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- `hxA` : x ∈ closure A
  -- `hxNotB` : x ∉ closure B
  have hClosureA := (mem_closure_iff).1 hxA
  -- The complement of `closure B` is an open neighbourhood of `x`.
  have hOpenT : IsOpen ((closure B)ᶜ : Set X) :=
    isClosed_closure.isOpen_compl
  have hxT : x ∈ (closure B)ᶜ := hxNotB
  -- Show that every open neighbourhood of `x` meets `A \ B`.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Consider `U ∩ (closure B)ᶜ`, an open neighbourhood of `x`.
  have hVopen : IsOpen (U ∩ (closure B)ᶜ) := hUopen.inter hOpenT
  have hxV : x ∈ U ∩ (closure B)ᶜ := And.intro hxU hxT
  -- Since `x ∈ closure A`, this neighbourhood meets `A`.
  have hNonempty := hClosureA (U ∩ (closure B)ᶜ) hVopen hxV
  rcases hNonempty with ⟨y, ⟨hyU, hyT⟩, hyA⟩
  -- `y` is in `A` and not in `closure B`, hence not in `B`.
  have hyNotB : (y : X) ∉ B := by
    intro hyB
    have : (y : X) ∈ closure B := subset_closure hyB
    exact hyT this
  have hyInDiff : (y : X) ∈ A \ B := And.intro hyA hyNotB
  -- Thus `y` lies in `U ∩ (A \ B)`.
  exact ⟨y, And.intro hyU hyInDiff⟩