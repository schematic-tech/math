import Schematic.Math.GraphTheory.Embedding.DartExtension.ReachabilityTransport

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u v

namespace LeafExtension

/-- Build a code on an extended dart type from the two fresh codes and the
code of an old dart. Keeping this eliminator transparent preserves computation
in the pivot-specific orbit quotients. -/
@[simp]
def ExtDart.code
    {α : Type u} {β : Type v}
    (newCode newEdgeCode : β) (oldCode : α → β) :
    ExtDart α → β
  | ExtDart.new => newCode
  | ExtDart.newEdge => newEdgeCode
  | ExtDart.old x => oldCode x

/-- A code constant on one-step links is constant on their reflexive-transitive
closure. This is the common quotient-code argument for leaf orbit counts. -/
theorem code_eq_of_reflTransGen
    {α : Type u} {β : Type v} {r : α → α → Prop}
    (code : α → β)
    (hlink : ∀ {x y}, r x y → code x = code y)
    {x y : α}
    (hxy : Relation.ReflTransGen r x y) :
    code x = code y :=
  hxy.apply_eq code (fun {_ _} h => hlink h)

end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
