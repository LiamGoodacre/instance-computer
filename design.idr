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

  _0 : RepVar 0 (k :: _) k
  _0 = Stop

  _1 : RepVar 1 (_ :: k :: _) k
  _1 = Pop _0

  _2 : RepVar 2 (_ :: _ :: k :: _) k
  _2 = Pop _1

  _3 : RepVar 3 (_ :: _ :: _ :: k :: _) k
  _3 = Pop _2


namespace Typing

  -- | Representation of types
  -- | TODO: environment
  data RepType : (scope : RepKinds n) -> (kindOfType : RepKind) -> Type where
    -- | Type variable
    Var    : RepVar i ks k -> RepType ks k
    -- | Universal quantification
    Forall : RepType (k :: ks) Star -> RepType ks Star
    -- | Type application
    App    : RepType ks (i :=> o) -> RepType ks i -> RepType ks o
    -- | Function type
    Fun    : RepType ks Star -> RepType ks Star -> RepType ks Star

  -- | Proper types have `Kind` `Star`
  ProperType : RepKinds n -> Type
  ProperType ks = RepType ks Star


namespace Filling
  -- | Sequence of types to fill in the arguments of a higher kinded type
  -- | TODO: environment
  data FilledKind : (typeVars : RepKinds n) -> (kind : RepKind) -> Type where
    Nil : FilledKind ts Star
    (::) : RepType ts d -> FilledKind ts c -> FilledKind ts (d :=> c)

  -- | Example: forall f a. Free f a
  filledKindExample : FilledKind [Star :=> Star, Star] ((Star :=> Star) :=> Star :=> Star)
  filledKindExample = [Var Stop, Var (Pop Stop)]


namespace DataTyping

  -- | Representation of a data type's constructors
  record RepCtor (dataKind : RepKind) where
    constructor MkCtor
    name      : String
    -- | All top level type variables
    typeVars  : RepKinds n
    -- | Constructor parameters with the `typeVars` and the data type in scope
    params    : List (ProperType (dataKind :: typeVars))
    -- | Type arguments of the resulting data type
    finalTypeArgs : FilledKind (dataKind :: typeVars) kind

  -- | Representation of data types
  record RepData where
    constructor MkData
    -- The `Kind` of the data type, e.g. kind of `Maybe` is `Arr Star Star`
    kind  : RepKind
    -- All constructors for the data type
    ctors : List (RepCtor kind)


namespace DataExamples

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
    [ MkCtor "nothing" [Star] []       [Var _1]
    , MkCtor "just"    [Star] [Var _1] [Var _1]
    ]

  -- Either : * -> * -> * where
  --   Left  : forall (l, r : *). l -> Either l r
  --   Right : forall (l, r : *). r -> Either l r
  either : RepData
  either = MkData (Star :=> Star :=> Star)
    [ MkCtor "left"  [Star, Star] [Var _1] [Var _1, Var _2]
    , MkCtor "right" [Star, Star] [Var _2] [Var _1, Var _2]
    ]

  -- Pair : * -> * -> * where
  --   Pair : forall (l, r : *). l -> r -> Pair l r
  pair : RepData
  pair = MkData (Star :=> Star :=> Star)
    [ MkCtor "pair" [Star, Star] [Var _1, Var _2] [Var _1, Var _2]
    ]

  -- Free : (* -> *) -> * -> * where
  --   Pure : forall (f : * -> *) (a : *). a -> Free f a
  --   Next : forall (f : * -> *) (a : *). f (Free f a) -> Free f a
  free : RepData
  free = MkData ((Star :=> Star) :=> Star :=> Star)
    [ MkCtor "pure" [Star :=> Star, Star] [Var _2] [Var _1, Var _2]
    , MkCtor "next" [Star :=> Star, Star]
             [App (Var _1) (App (App (Var _0) (Var _1)) (Var _2))]
             [Var _1, Var _2]
    ]



  {-
    POSSIBLE CONSIDERATIONS
    want to guarantee that computed instances can
      only use type args - cannot inspect types of parameters
      specify constraints: generally, for particular type arguments of higher kinded types, etc
      fail deriving: data type not compatible, etc
  -}

