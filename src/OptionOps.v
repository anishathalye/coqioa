Section Main.

  Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
    match xo with
    | None => None
    | Some x => Some (f x)
    end.

End Main.
