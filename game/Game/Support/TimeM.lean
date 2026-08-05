import Mathlib

/-!
# TimeM: Time Complexity Monad

Ported from `RequestProject/TimeM.lean` (itself a faithful copy of the `TimeM` monad from
`Cslib`, adapted to build against a plain `import Mathlib`). `TimeM T α` represents a
computation that produces a value of type `α` and tracks its time cost of type `T` (usually
`ℕ`, counting operations). This is pure infrastructure for the Clockwork world's cost
proofs — no level plays anything from this file directly, but Labs 11–17's algorithms and
their `.time` cost proofs are stated in terms of it.

## Notation
- **`✓`** : a tick of time, see `tick`.
- **`⟪tm⟫`** : extract the pure value from a `TimeM` computation (notation for `tm.ret`).
-/

namespace Cslib.Algorithms.Lean

/-- A monad for tracking time complexity of computations. `TimeM T α` represents a computation
that returns a value of type `α` and accumulates a time cost (represented as a type `T`,
typically `ℕ`). -/
@[ext]
structure TimeM (T : Type*) (α : Type*) where
  /-- The return value of the computation. -/
  ret : α
  /-- The accumulated time cost of the computation. -/
  time : T

namespace TimeM

/-- Lifts a pure value into a `TimeM` computation with zero time cost.

Prefer to use `pure` instead of `TimeM.pure`. -/
protected def pure [Zero T] {α} (a : α) : TimeM T α :=
  ⟨a, 0⟩

instance [Zero T] : Pure (TimeM T) where
  pure := TimeM.pure

/-- Sequentially composes two `TimeM` computations, summing their time costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance [Add T] : Bind (TimeM T) where
  bind := TimeM.bind

instance : Functor (TimeM T) where
  map f x := ⟨f x.ret, x.time⟩

instance [Add T] : Seq (TimeM T) where
  seq f x := ⟨f.ret (x ()).ret, f.time + (x ()).time⟩

instance [Add T] : SeqLeft (TimeM T) where
  seqLeft x y := ⟨x.ret, x.time + (y ()).time⟩

instance [Add T] : SeqRight (TimeM T) where
  seqRight x y := ⟨(y ()).ret, x.time + (y ()).time⟩

instance [AddZero T] : Monad (TimeM T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

@[simp, grind =] theorem ret_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).ret = a := rfl
@[simp, grind =] theorem ret_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).ret = (f m.ret).ret := rfl
@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).ret = f x.ret := rfl
@[simp] theorem ret_seqRight {α} (x : TimeM T α) (y : Unit → TimeM T β) [Add T] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl
@[simp] theorem ret_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl
@[simp] theorem ret_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl

@[simp, grind =] theorem time_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl
@[simp, grind =] theorem time_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).time = 0 := rfl
@[simp, grind =] theorem time_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).time = x.time := rfl
@[simp] theorem time_seqRight {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqRight.seqRight x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).time = f.time + (x ()).time := rfl

/-- `TimeM` is lawful so long as addition in the cost is associative and absorbs zero. -/
instance [AddMonoid T] : LawfulMonad (TimeM T) := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp only [ret_bind, ret_pure, time_bind, time_pure, zero_add])
  (bind_assoc := fun _ _ _ => by ext <;> simp only [time_bind, ret_bind, add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp only [ret_seqLeft, ret_bind, ret_pure, time_seqLeft, time_bind, time_pure, add_zero])
  (bind_pure_comp := fun _ _ => by ext <;> simp only [ret_bind, ret_pure, ret_map, time_bind, time_pure, add_zero, time_map])

/-- Creates a `TimeM` computation with a time cost. -/
def tick (c : T) : TimeM T PUnit := ⟨.unit, c⟩

@[simp, grind =] theorem ret_tick (c : T) : (tick c).ret = () := rfl
@[simp, grind =] theorem time_tick (c : T) : (tick c).time = c := rfl

/-- `✓[c] x` adds `c` ticks, then executes `x`. -/
macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do TimeM.tick $c; $body:doElem)

/-- `✓ x` is a shorthand for `✓[1] x`, which adds one tick and executes `x`. -/
macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

/-- Notation for extracting the return value from a `TimeM` computation: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

end TimeM
end Cslib.Algorithms.Lean
