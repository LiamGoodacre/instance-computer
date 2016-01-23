import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers


namespace Kinding

  -- | Possible kinds of type
  data RepKind
    = Arr RepKind RepKind
    | Star
    -- TODO: add Constraint, Row, etc

  infixr 4 :=>
  (:=>) : RepKind -> RepKind -> RepKind
  (:=>) = Arr

  RepKinds : Nat -> Type
  RepKinds n = Vect n RepKind


namespace VariableReferencing

  -- | Reference a variable in scope of a given `Kind`
  data Item : Fin n -> Vect n t -> t -> Type where
    Stop : Item FZ (k :: ks) k
    Pop  : Item i ks k -> Item (FS i) (o :: ks) k

  fromFin : (i : Fin n) -> (ks : RepKinds n) -> Item i ks (Vect.index i ks)
  fromFin FZ (v :: vs) = Stop
  fromFin (FS i) (v :: vs) = Pop (fromFin i vs)


namespace Typing

  -- | Representation of types
  data RepType : (env : RepKinds e) -> (scope : RepKinds n) -> (kindOfType : RepKind) -> Type where
    -- | Type variable
    Var : Item i ks k -> RepType es ks k
    -- | Universal quantification
    Forall : RepType es (ks ++ [k]) Star -> RepType es ks Star
    -- | Type application
    App : RepType es ks (i :=> o) -> RepType es ks i -> RepType es ks o
    -- | Function type
    Fun : RepType es ks Star -> RepType es ks Star -> RepType es ks Star
    -- | Reference types in the environment
    Other : Item i es e -> RepType es ks e

  -- | Proper types have `Kind` `Star`
  ProperType : RepKinds e -> RepKinds n -> Type
  ProperType es ks = RepType es ks Star

  var : (i : Fin n) -> RepType es ks (Vect.index i ks)
  var i {ks} = Var (fromFin i ks)

  infix 5 :$
  (:$) : RepType es ks (i :=> o) -> RepType es ks i -> RepType es ks o
  (:$) = App

  infixl 4 :->
  (:->) : ProperType es ks -> ProperType es ks -> ProperType es ks
  (:->) = Fun

  other : (i : Fin n) -> RepType es ks (Vect.index i es)
  other i {es} = Other (fromFin i es)


namespace Filling

  -- | Sequence of types to fill in the arguments of a higher kinded type
  data FilledKind : (env : RepKinds e) -> (typeVars : RepKinds n) -> (kind : RepKind) -> Type where
    Nil  : FilledKind es ts Star
    (::) : RepType es ts d -> FilledKind es ts c -> FilledKind es ts (d :=> c)

  -- | Example: forall f a. Free f a
  filledKindExample : FilledKind [] [Star :=> Star, Star] ((Star :=> Star) :=> Star :=> Star)
  filledKindExample = [var 0, var 1]


namespace DataTyping

  -- | Representation of a data type's constructors
  record RepCtor (dataKind : RepKind) where
    constructor MkCtor
    name : String
    -- | Available types in the environment
    environment : RepKinds e
    -- | All top level type variables
    typeVars : RepKinds n
    -- | Constructor parameters with the `typeVars` and the data type in scope
    params : Vect paramCount (ProperType environment (dataKind :: typeVars))
    -- | Type arguments of the resulting data type
    finalTypeArgs : FilledKind environment (dataKind :: typeVars) dataKind

  -- | Representation of data types
  record RepData where
    constructor MkData
    -- The `Kind` of the data type, e.g. kind of `Maybe` is `Arr Star Star`
    kind : RepKind
    -- All constructors for the data type
    ctors : Vect sumCount (RepCtor kind)

  datatype : (kind : RepKind) -> Vect n (RepCtor kind) -> RepData
  datatype = MkData

  self : RepType es (k :: ks) k
  self = var 0


namespace Valuing

  data RepArg : RepType es ks Star -> Type where
    VarArg : RepArg (Var v)
    EnvArg : RepArg (Other e)

  data RepValue : (rep : RepData) ->
                  (env : RepKinds e) ->
                  FilledKind env vars (kind rep) ->
                  Type where
    MkValue : (rep : RepData) ->
              Item i (ctors rep) ctor ->
              (args : All RepArg (params ctor)) ->
              RepValue rep (environment ctor) (finalTypeArgs ctor)


namespace DataExamples

  -- Unit : * where
  --   Unit : Unit
  unit : RepData
  unit = datatype Star
    [ MkCtor "unit" [] [] [] []
    ]

  -- uuu : RepValue unit [] []
  -- uuu = MkValue unit (fromFin 0) [] []

  -- Bool : * where
  --   True : Bool
  --   False : Bool
  bool : RepData
  bool = datatype Star
    [ MkCtor "true"  [] [] [] []
    , MkCtor "false" [] [] [] []
    ]

  -- true : RepValue bool [] []
  -- true = MkValue bool (fromFin 0) [] []

  -- Maybe : * -> * where
  --   Nothing : forall (t : *). Maybe t
  --   Just    : forall (t : *). t -> Maybe t
  maybe : RepData
  maybe = datatype (Star :=> Star)
    [ MkCtor "nothing" [] [Star] []      [var 1]
    , MkCtor "just"    [] [Star] [var 1] [var 1]
    ]

  -- Either : * -> * -> * where
  --   Left  : forall (l, r : *). l -> Either l r
  --   Right : forall (l, r : *). r -> Either l r
  either : RepData
  either = datatype (Star :=> Star :=> Star)
    [ MkCtor "left"  [] [Star, Star] [var 1] [var 1, var 2]
    , MkCtor "right" [] [Star, Star] [var 2] [var 1, var 2]
    ]

  -- Pair : * -> * -> * where
  --   Pair : forall (l, r : *). l -> r -> Pair l r
  pair : RepData
  pair = datatype (Star :=> Star :=> Star)
    [ MkCtor "pair" [] [Star, Star] [var 1, var 2] [var 1, var 2]
    ]

  -- List : * -> * where
  --   Nil  : forall (t : *). List t
  --   Cons : forall (t : *). t -> List t -> List t
  list : RepData
  list = datatype (Star :=> Star)
    [ MkCtor "nil"  [] [Star] [] [var 1]
    , MkCtor "cons" [] [Star] [var 1, self :$ var 1] [var 1]
    ]

  -- Coyoneda : (* -> *) -> * -> * where
  --   Coyo : forall (f : * -> *) (a, b : *). (b -> a) -> (f b) -> Coyoneda f a
  coyoneda : RepData
  coyoneda = datatype ((Star :=> Star) :=> Star :=> Star)
    [ MkCtor "coyo" [] [Star :=> Star, Star, Star]
                       [var 3 :-> var 2, var 1 :$ var 2]
                       [var 1, var 2]
    ]

  -- Free : (* -> *) -> * -> * where
  --   Pure : forall (f : * -> *) (a : *). a -> Free f a
  --   Next : forall (f : * -> *) (a : *). f (Free f a) -> Free f a
  free : RepData
  free = datatype ((Star :=> Star) :=> Star :=> Star)
    [ MkCtor "pure" [] [Star :=> Star, Star] [var 2] [var 1, var 2]
    , MkCtor "next" [] [Star :=> Star, Star]
                       [var 1 :$ ((self :$ var 1) :$ var 2)]
                       [var 1, var 2]
    ]

  -- Exists : (* -> *) -> * where
  --   MkExists : forall (p : * -> *). (forall r. (forall i. p i -> r) -> r) -> Exists p
  exists : RepData
  exists = datatype ((Star :=> Star) :=> Star)
    [ MkCtor "mkExists" [] [Star :=> Star]
                           [Forall (Forall ((var 1 :$ var 3) :-> var 2) :-> var 2)]
                           [var 1]
    ]


  -- | Here we have a reference to `String : *`
  -- FullName : * where
  --   MkFullName : String -> String -> FullName
  fullName : RepData
  fullName = datatype Star
    [ MkCtor "mkFullName" [Star] [] [other 0, other 0] []
    ]


  {-
    POSSIBLE CONSIDERATIONS
    want to guarantee that computed instances can
      only use type args - cannot inspect types of parameters
      specify constraints: generally, for particular type arguments of higher kinded types, etc
      fail deriving: data type not compatible, etc
  -}

