import Data.Vect
import Data.Fin

namespace Kinding

  -- | Possible kinds of type
  data RepKind
    = (:=>) RepKind RepKind
    | Star
    -- TODO: add Constraint, Row, etc

  infixr 4 :=>

  RepKinds : Nat -> Type
  RepKinds n = Vect n RepKind


namespace VariableReferencing

  -- | Reference a variable in scope of a given `Kind`
  data RepVar : Fin n -> (scope : RepKinds n) -> RepKind -> Type where
    Stop : RepVar FZ (k :: ks) k
    Pop  : RepVar i ks k -> RepVar (FS i) (o :: ks) k

  fromFin : (i : Fin n) -> (ks : RepKinds n) -> RepVar i ks (Vect.index i ks)
  fromFin FZ (v :: vs) = Stop
  fromFin (FS i) (v :: vs) = Pop (fromFin i vs)


namespace Typing

  -- | Representation of types
  -- | TODO: environment
  data RepType : (scope : RepKinds n) -> (kindOfType : RepKind) -> Type where
    -- | Type variable
    Var : RepVar i ks k -> RepType ks k
    -- | Universal quantification
    Forall : RepType (k :: ks) Star -> RepType ks Star
    -- | Type application
    App : RepType ks (i :=> o) -> RepType ks i -> RepType ks o
    -- | Function type
    (:->) : RepType ks Star -> RepType ks Star -> RepType ks Star

  infixl 4 :->

  -- | Proper types have `Kind` `Star`
  ProperType : RepKinds n -> Type
  ProperType ks = RepType ks Star

  -- var : (i : Fin n) -> {auto ks : RepKinds n} -> RepVar i ks (Vect.index i ks)
  var : (i : Fin n) -> RepType ks (Vect.index i ks)
  var i {ks} = Var (fromFin i ks)


namespace Filling

  -- | Sequence of types to fill in the arguments of a higher kinded type
  -- | TODO: environment
  data FilledKind : (typeVars : RepKinds n) -> (kind : RepKind) -> Type where
    Nil  : FilledKind ts Star
    (::) : RepType ts d -> FilledKind ts c -> FilledKind ts (d :=> c)

  -- | Example: forall f a. Free f a
  filledKindExample : FilledKind [Star :=> Star, Star] ((Star :=> Star) :=> Star :=> Star)
  filledKindExample = [var 0, var 1]


namespace DataTyping

  -- | Representation of a data type's constructors
  record RepCtor (dataKind : RepKind) where
    constructor MkCtor
    name : String
    -- | All top level type variables
    typeVars : RepKinds n
    -- | Constructor parameters with the `typeVars` and the data type in scope
    params : List (ProperType (dataKind :: typeVars))
    -- | Type arguments of the resulting data type
    finalTypeArgs : FilledKind (dataKind :: typeVars) dataKind

  -- | Representation of data types
  record RepData where
    constructor MkData
    -- The `Kind` of the data type, e.g. kind of `Maybe` is `Arr Star Star`
    kind : RepKind
    -- All constructors for the data type
    ctors : List (RepCtor kind)


namespace DataExamples

  -- Unit : * where
  --   Unit : Unit
  unit : RepData
  unit = MkData Star
    [ MkCtor "unit" [] [] []
    ]

  -- Bool : * where
  --   True : Bool
  --   False : Bool
  bool : RepData
  bool = MkData Star
    [ MkCtor "true" [] [] []
    , MkCtor "false" [] [] []
    ]

  -- Maybe : * -> * where
  --   Nothing : forall (t : *). Maybe t
  --   Just    : forall (t : *). t -> Maybe t
  maybe : RepData
  maybe = MkData (Star :=> Star)
    [ MkCtor "nothing" [Star] []      [var 1]
    , MkCtor "just"    [Star] [var 1] [var 1]
    ]

  -- Either : * -> * -> * where
  --   Left  : forall (l, r : *). l -> Either l r
  --   Right : forall (l, r : *). r -> Either l r
  either : RepData
  either = MkData (Star :=> Star :=> Star)
    [ MkCtor "left"  [Star, Star] [var 1] [var 1, var 2]
    , MkCtor "right" [Star, Star] [var 2] [var 1, var 2]
    ]

  -- Pair : * -> * -> * where
  --   Pair : forall (l, r : *). l -> r -> Pair l r
  pair : RepData
  pair = MkData (Star :=> Star :=> Star)
    [ MkCtor "pair" [Star, Star] [var 1, var 2] [var 1, var 2]
    ]

  -- Free : (* -> *) -> * -> * where
  --   Pure : forall (f : * -> *) (a : *). a -> Free f a
  --   Next : forall (f : * -> *) (a : *). f (Free f a) -> Free f a
  free : RepData
  free = MkData ((Star :=> Star) :=> Star :=> Star)
    [ MkCtor "pure" [Star :=> Star, Star] [var 2] [var 1, var 2]
    , MkCtor "next" [Star :=> Star, Star]
             [App (var 1) (App (App (var 0) (var 1)) (var 2))]
             [var 1, var 2]
    ]

  -- Exists : (* -> *) -> * where
  --   MkExists : forall (p : * -> *). (forall r. (forall i. p i -> r) -> r) -> Exists p
  exists : RepData
  exists = MkData ((Star :=> Star) :=> Star)
    [ MkCtor "mkExists" [Star :=> Star]
             [ Forall (Forall (App (var 2) (var 0) :-> var 1) :-> var 0)
             ] [var 1]
    ]

  {-
    POSSIBLE CONSIDERATIONS
    want to guarantee that computed instances can
      only use type args - cannot inspect types of parameters
      specify constraints: generally, for particular type arguments of higher kinded types, etc
      fail deriving: data type not compatible, etc
  -}

