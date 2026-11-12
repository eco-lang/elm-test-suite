module StaticBasis.Json exposing
    ( Basis
    , DefaultImport
    , Exposing(..)
    , ExposedItem(..)
    , Interface
    , OperatorRow
    , TypeNameRow
    , basisDecoder
    , encodeBasis
    )

{-| `definition/mechanisation/static-basis.json` (plans/lean-full-definition/step-07-classify.md,
section 5.1): the encoder the extractor uses and the decoder the classifier (and step 9's Lean
writer) use.
-}

import Json.Decode as D exposing (Decoder)
import Json.Encode as E
import StaticBasis.Latex exposing (Scheme, TEntry, Ty(..), VEntry)


type alias TypeNameRow =
    { key : String, macro : String, arity : Int, boundTo : List String, kind : String }


type alias Interface =
    { module_ : String, library : String, te : List TEntry, ve : List VEntry, ops : List String }


type alias OperatorRow =
    { op : String, rank : Int, standsFor : String, declaredBy : String, label : Maybe String, scheme : Scheme, status : String }


type ExposedItem
    = ExpValue String
    | ExpOp String
    | ExpType String
    | ExpTypeAll String


type Exposing
    = ExposingAll
    | ExposingItems (List ExposedItem)


type alias DefaultImport =
    { module_ : String, as_ : Maybe String, exposing_ : Maybe Exposing }


type alias Basis =
    { sources : List ( String, String )
    , typeNames : List TypeNameRow
    , e0 : { te : List TEntry, ve : List VEntry }
    , modules : List Interface
    , operators : List OperatorRow
    , hidden : List { module_ : String, name : String, kind : String, typeName : Maybe String, note : Maybe String }
    , defaultImports : List DefaultImport
    }



-- ENCODING


encodeTy : Ty -> E.Value
encodeTy t =
    case t of
        TyVar a ->
            E.object [ ( "var", E.string a ) ]

        TyCon c args ->
            E.object [ ( "con", E.string c ), ( "args", E.list encodeTy args ) ]

        TyFn a b ->
            E.object [ ( "fn", E.list encodeTy [ a, b ] ) ]

        TyRecord fs ->
            E.object
                [ ( "record", E.list (\( l, ft ) -> E.list identity [ E.string l, encodeTy ft ]) fs )
                , ( "tail", E.null )
                ]


encodeScheme : Scheme -> E.Value
encodeScheme s =
    E.object [ ( "forall", E.list E.string s.forall ), ( "body", encodeTy s.body ) ]


firstLabel : List String -> E.Value
firstLabel ls =
    case List.filter (\l -> l /= "*") ls of
        l :: _ ->
            E.string l

        [] ->
            E.null


encodeVE : VEntry -> E.Value
encodeVE e =
    E.object
        [ ( "name", E.string e.name )
        , ( "label", firstLabel e.labels )
        , ( "scheme", encodeScheme e.scheme )
        , ( "status", E.string e.status )
        ]


encodeTE : TypeNameRow -> TEntry -> E.Value
encodeTE row e =
    let
        params =
            List.map (\i -> "a" ++ String.fromInt i) (List.range 1 row.arity)
    in
    E.object
        [ ( "tycon", E.string e.tycon )
        , ( "label", firstLabel e.labels )
        , ( "fcn", E.object [ ( "params", E.list E.string params ), ( "body", encodeTy (TyCon e.typeName (List.map TyVar params)) ) ] )
        , ( "VE", E.list encodeVE e.ve )
        ]


encodeExposing : Maybe Exposing -> E.Value
encodeExposing ex =
    case ex of
        Nothing ->
            E.null

        Just ExposingAll ->
            E.object [ ( "all", E.bool True ) ]

        Just (ExposingItems items) ->
            E.object
                [ ( "items"
                  , E.list
                        (\it ->
                            case it of
                                ExpValue x ->
                                    E.object [ ( "value", E.string x ) ]

                                ExpOp o ->
                                    E.object [ ( "op", E.string o ) ]

                                ExpType t ->
                                    E.object [ ( "type", E.string t ) ]

                                ExpTypeAll t ->
                                    E.object [ ( "typeAll", E.string t ) ]
                        )
                        items
                  )
                ]


encodeBasis : Basis -> String
encodeBasis b =
    let
        rowOf key =
            b.typeNames |> List.filter (\r -> r.key == key) |> List.head |> Maybe.withDefault { key = key, macro = "", arity = 0, boundTo = [], kind = "" }

        encTE e =
            encodeTE (rowOf e.typeName) e
    in
    E.encode 2
        (E.object
            [ ( "generatedBy", E.string "definition/tools/src/ExtractStaticBasis.elm" )
            , ( "sources", E.list (\( p, sha ) -> E.object [ ( "path", E.string p ), ( "sha256", E.string sha ) ]) b.sources )
            , ( "typeNames"
              , E.list
                    (\r ->
                        E.object
                            [ ( "key", E.string r.key )
                            , ( "macro", E.string ("\\" ++ r.macro) )
                            , ( "arity", E.int r.arity )
                            , ( "boundTo", E.list E.string r.boundTo )
                            , ( "kind", E.string r.kind )
                            ]
                    )
                    b.typeNames
              )
            , ( "E0", E.object [ ( "TE", E.list encTE b.e0.te ), ( "VE", E.list encodeVE b.e0.ve ) ] )
            , ( "modules"
              , E.list
                    (\m ->
                        E.object
                            [ ( "module", E.string m.module_ )
                            , ( "library", E.string m.library )
                            , ( "TE", E.list encTE m.te )
                            , ( "VE", E.list encodeVE m.ve )
                            , ( "ops", E.list E.string m.ops )
                            ]
                    )
                    b.modules
              )
            , ( "operators"
              , E.list
                    (\o ->
                        E.object
                            [ ( "op", E.string o.op )
                            , ( "rank", E.int o.rank )
                            , ( "standsFor", E.string o.standsFor )
                            , ( "declaredBy", E.string o.declaredBy )
                            , ( "label", o.label |> Maybe.map E.string |> Maybe.withDefault E.null )
                            , ( "scheme", encodeScheme o.scheme )
                            , ( "status", E.string o.status )
                            ]
                    )
                    b.operators
              )
            , ( "hidden"
              , E.list
                    (\h ->
                        E.object
                            ([ ( "module", E.string h.module_ )
                             , ( "name", E.string h.name )
                             , ( "kind", E.string h.kind )
                             ]
                                ++ (if h.kind == "constructor" then
                                        [ ( "typeName", h.typeName |> Maybe.map E.string |> Maybe.withDefault E.null ) ]

                                    else
                                        []
                                   )
                                ++ (h.note |> Maybe.map (\n -> [ ( "note", E.string n ) ]) |> Maybe.withDefault [])
                            )
                    )
                    b.hidden
              )
            , ( "PE0", E.list identity [] )
            , ( "defaultImports"
              , E.list
                    (\d ->
                        E.object
                            [ ( "module", E.string d.module_ )
                            , ( "as", d.as_ |> Maybe.map E.string |> Maybe.withDefault E.null )
                            , ( "exposing", encodeExposing d.exposing_ )
                            ]
                    )
                    b.defaultImports
              )
            ]
        )
        ++ "\n"



-- DECODING (the parts the classifier reads)


tyDecoder : Decoder Ty
tyDecoder =
    D.oneOf
        [ D.field "var" D.string |> D.map TyVar
        , D.map2 TyCon (D.field "con" D.string) (D.field "args" (D.list (D.lazy (\_ -> tyDecoder))))
        , D.field "fn" (D.list (D.lazy (\_ -> tyDecoder)))
            |> D.andThen
                (\ts ->
                    case ts of
                        [ a, b ] ->
                            D.succeed (TyFn a b)

                        _ ->
                            D.fail "fn needs two types"
                )
        , D.field "record"
            (D.list
                (D.map2 Tuple.pair (D.index 0 D.string) (D.index 1 (D.lazy (\_ -> tyDecoder))))
            )
            |> D.map TyRecord
        ]


schemeDecoder : Decoder Scheme
schemeDecoder =
    D.map2 Scheme (D.field "forall" (D.list D.string)) (D.field "body" tyDecoder)


veDecoder : Decoder VEntry
veDecoder =
    D.map4 VEntry
        (D.field "name" D.string)
        (D.field "label" (D.nullable D.string) |> D.map (Maybe.map List.singleton >> Maybe.withDefault []))
        (D.field "scheme" schemeDecoder)
        (D.field "status" D.string)


teDecoder : Decoder TEntry
teDecoder =
    D.map4 TEntry
        (D.field "tycon" D.string)
        (D.field "label" (D.nullable D.string) |> D.map (Maybe.map List.singleton >> Maybe.withDefault []))
        (D.field "fcn" (D.field "body" (D.field "con" D.string)))
        (D.field "VE" (D.list veDecoder))


exposingDecoder : Decoder (Maybe Exposing)
exposingDecoder =
    D.nullable
        (D.oneOf
            [ D.field "all" D.bool |> D.map (\_ -> ExposingAll)
            , D.field "items"
                (D.list
                    (D.oneOf
                        [ D.field "value" D.string |> D.map ExpValue
                        , D.field "op" D.string |> D.map ExpOp
                        , D.field "type" D.string |> D.map ExpType
                        , D.field "typeAll" D.string |> D.map ExpTypeAll
                        ]
                    )
                )
                |> D.map ExposingItems
            ]
        )


basisDecoder : Decoder Basis
basisDecoder =
    D.map7 Basis
        (D.field "sources" (D.list (D.map2 Tuple.pair (D.field "path" D.string) (D.field "sha256" D.string))))
        (D.field "typeNames"
            (D.list
                (D.map5 TypeNameRow
                    (D.field "key" D.string)
                    (D.field "macro" D.string)
                    (D.field "arity" D.int)
                    (D.field "boundTo" (D.list D.string))
                    (D.field "kind" D.string)
                )
            )
        )
        (D.field "E0" (D.map2 (\te ve -> { te = te, ve = ve }) (D.field "TE" (D.list teDecoder)) (D.field "VE" (D.list veDecoder))))
        (D.field "modules"
            (D.list
                (D.map5 Interface
                    (D.field "module" D.string)
                    (D.field "library" D.string)
                    (D.field "TE" (D.list teDecoder))
                    (D.field "VE" (D.list veDecoder))
                    (D.field "ops" (D.list D.string))
                )
            )
        )
        (D.field "operators"
            (D.list
                (D.map7 OperatorRow
                    (D.field "op" D.string)
                    (D.field "rank" D.int)
                    (D.field "standsFor" D.string)
                    (D.field "declaredBy" D.string)
                    (D.field "label" (D.nullable D.string))
                    (D.field "scheme" schemeDecoder)
                    (D.field "status" D.string)
                )
            )
        )
        (D.field "hidden"
            (D.list
                (D.map5 (\m n k t no -> { module_ = m, name = n, kind = k, typeName = t, note = no })
                    (D.field "module" D.string)
                    (D.field "name" D.string)
                    (D.field "kind" D.string)
                    (D.maybe (D.field "typeName" D.string))
                    (D.maybe (D.field "note" D.string))
                )
            )
        )
        (D.field "defaultImports"
            (D.list
                (D.map3 DefaultImport
                    (D.field "module" D.string)
                    (D.field "as" (D.nullable D.string))
                    (D.field "exposing" exposingDecoder)
                )
            )
        )
