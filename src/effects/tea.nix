# nix-effects tea: The Elm Architecture
#
# Elm's Model-View-Update loop (Czaplicki 2012, Evans 2019) expressed as a
# nix-effects algebraic effect handler.  Every TEA concept maps directly:
#
#   Elm                         nix-effects
#   ─────────────────────────── ─────────────────────────────────────────
#   Program flags model msg     { init, update, view, subscriptions }
#   Cmd msg                     Computation [msg]   (effectful, yields msgs)
#   Sub msg                     { effectName = param -> msg }
#   Html/View                   any attrset (domain-specific)
#   Browser.sandbox             tea.run
#   Browser.element/document    tea.scope (outer effects available to Cmds)
#
# Beyond vanilla TEA, nix-effects adds two composition primitives:
#
#   handlers : model -> { effectName = handler }   (per-component effect scope)
#   nest / tea { … }                               (automatic child-aware components)
#
# `handlers` lets a component intercept algebraic effects emitted from its
# Cmds.  The handler set is re-derived from the *updated* model after every
# dispatch, so components can activate or deactivate handlers dynamically.
# Children's `handlers` bubble up to all ancestors automatically.
#
# `nest` (aliased as the `tea` __functor) derives a fully child-aware
# TEA component from a plain attribute set.  Function-valued extra attrs
# become view fragments; attrset-valued extra attrs become nested child
# components whose init/update/subscriptions/view/handlers are composed
# automatically and recursively.
#
# References:
#   Czaplicki (2012) "Elm: Concurrent FRP for Functional GUIs"
#   Evans (2019) "The Elm Architecture" https://guide.elm-lang.org/architecture/
{ fx, api, lib, ... }:

let
  inherit (fx.kernel) pure bind send;
  inherit (fx.trampoline) handle rotate;
  inherit (api) mk;

  # Extract tag/payload from a single-key attrset { Tag = payload }.
  tagOf     = msg: builtins.head (builtins.attrNames msg);
  payloadOf = msg: msg.${tagOf msg};

  # Add cmd = Cmd.none when a handler returns only { model }.
  normResult = r: if r ? cmd then r else r // { cmd = pure []; };

  # Convert Cmd (Computation [msg]) into sequenced tea:dispatch sends.
  processCmd = cmd:
    bind cmd (msgs:
      builtins.foldl'
        (acc: m: bind acc (_: send "tea:dispatch" m))
        (pure null) msgs);

  # Internal handler set for a TEA program. State shape: { model, view }.
  mkHandlers_ = program:
    let
      subs = program.subscriptions or (_: []);
      view = program.view;
      getHandlers = program.handlers or (_: {});
    in {
      "tea:dispatch" = { param, state }:
        let
          r             = normResult (program.update param state.model);
          newState      = { model = r.model; view = view r.model; };
          activeHandlers = getHandlers r.model;
          resume =
            if activeHandlers == {}
            then processCmd r.cmd
            else bind
                   (rotate { handlers = activeHandlers; state = null; } (processCmd r.cmd))
                   ({ value, ... }: pure value);
        in { inherit resume; state = newState; };

      # Broadcast: call toMsg for every sub whose effect name matches.
      "tea:sub" = { param, state }:
        let
          matched  = builtins.filter (s: tagOf s == tagOf param) (subs state.model);
          dispatch = builtins.foldl'
            (acc: s: bind acc (_: send "tea:dispatch" ((payloadOf s) (payloadOf param))))
            (pure null) matched;
        in { resume = dispatch; inherit state; };

      "tea:getModel" = { state, ... }: { resume = state.model; inherit state; };
      "tea:getView"  = { state, ... }: { resume = state.view;  inherit state; };
    };

  # ── Cmd ──────────────────────────────────────────────────────────────────

  Cmd = mk {
    doc = ''
      In Elm, `Cmd msg` describes work the runtime should do (HTTP, random,
      ports).  Here, `Cmd msg = Computation [msg]` — an effectful computation
      that yields zero or more messages fed back through `update`.

      This keeps the TEA loop purely functional: `update` returns data
      describing effects, never executing them directly.  When a component
      declares a `handlers` field, those effect handlers intercept effects
      sent *from* its Cmds before they escape to the outer scope — allowing
      components to own their own side-effect vocabulary.

      ```
      Cmd.none          : Cmd msg              -- do nothing
      Cmd.msg m         : Cmd msg              -- immediately re-dispatch m
      Cmd.batch cmds    : [Cmd msg] -> Cmd msg -- run all, concat results
      Cmd.map f cmd     : (a -> b) -> Cmd a -> Cmd b
      ```
    '';
    value = {
      none  = pure [];
      msg   = m: pure [ m ];
      batch = cmds:
        builtins.foldl' (acc: cmd:
          bind acc (ms1: bind cmd (ms2: pure (ms1 ++ ms2)))
        ) (pure []) cmds;
      map = f: cmd: bind cmd (msgs: pure (map f msgs));
    };
    tests = {
      "cmd-none-msg-batch" = {
        expr =
          let c = Cmd.value.batch [ Cmd.value.none (Cmd.value.msg "A") (Cmd.value.msg "B") ];
          in (handle { handlers = {}; } c).value;
        expected = [ "A" "B" ];
      };
      "cmd-map" = {
        expr =
          let c = Cmd.value.map (m: "${m}!") (Cmd.value.batch [ (Cmd.value.msg "A") (Cmd.value.msg "B") ]);
          in (handle { handlers = {}; } c).value;
        expected = [ "A!" "B!" ];
      };
    };
  };

  # ── Sub ──────────────────────────────────────────────────────────────────

  Sub = mk {
    doc = ''
      In Elm, subscriptions declare interest in external events (time, keyboard,
      WebSocket).  Here they are `{ effectName = param -> msg }` — the same
      single-key attrset shape used for messages.  The runtime re-evaluates
      `subscriptions model` after every update, so the active set is always
      current (dynamic subscribe/unsubscribe).

      A single `Sub.fire` call broadcasts to *all* matching subscriptions,
      mirroring Elm's subscription semantics.  When using `tea.nest`, child
      subscriptions are aggregated automatically and mapped through
      `{ childName = … }` so firing a shared clock event reaches every
      interested component without any parent wiring.

      ```
      Sub.none           : [Sub]
      Sub.batch          : [[Sub]] -> [Sub]        -- aggregate children's subs
      Sub.map f sub      : (a -> b) -> Sub a -> Sub b
      Sub.fire { e = p } : Computation null        -- fire event e with param p
      ```
    '';
    value = {
      none  = [];
      batch = lib.concatLists;
      map   = f: sub: { ${tagOf sub} = p: f ((payloadOf sub) p); };
      fire  = send "tea:sub";
    };
    tests = {
      "sub-none-batch-map" = {
        # none=[]; batch flattens; map wraps toMsgFn.
        expr =
          let
            s = Sub.value.map (m: "P:${m}") { tick = _: "Child"; };
            r = Sub.value.batch [ Sub.value.none [ s ] ];
          in { len = builtins.length r; effect = tagOf s; msg = (payloadOf s) null; };
        expected = { len = 1; effect = "tick"; msg = "P:Child"; };
      };
      "sub-fire" = {
        # Sub.fire { effectName = param } delivers the message through a running program.
        expr =
          let
            prog = {
              init   = _: { model = 0; };
              update = on.value { Tick = _: n: { model = n + 1; }; };
              view   = n: { n = n; };
              subscriptions = _: [{ tick = _: { Tick = null; }; }];
            };
            s0 = { model = 0; view = { n = 0; }; };
            r  = handle { handlers = mkHandlers.value prog; state = s0; } (Sub.value.fire { tick = null; });
          in r.state.model;
        expected = 1;
      };
    };
  };

  # ── on ───────────────────────────────────────────────────────────────────

  on = mk {
    doc = ''
      The `update` function in Elm is a `case msg of` expression.  `tea.on`
      provides the same dispatch table in Nix: messages are single-key attrsets
      `{ Tag = payload }` and each entry handles one tag.

      Unknown tags are a silent no-op (model unchanged, Cmd.none), matching
      Elm's exhaustive-but-extensible design.  `cmd` is optional in handlers —
      omitting it is equivalent to returning `Cmd.none`.

      When using `tea.nest`, child components receive messages whose tag equals
      the child's attribute name: `{ counter = { Inc = null } }` is routed to
      the `counter` child automatically, so `tea.on` in the parent only needs
      to handle parent-level messages.

      ```nix
      update = tea.on {
        Increment = _: model: { model = model + 1; };
        Add       = n: model: { model = model + n; };
        Reset     = _: _:     { model = 0; cmd = Cmd.msg { Log = null; }; };
      };
      ```
    '';
    value = handlers: msg: model:
      let
        tag = tagOf msg;
        h   = handlers.${tag} or null;
      in normResult (
        if h != null then h (payloadOf msg) model
        else { inherit model; }
      );
    tests = {
      "on-routing-and-payload" = {
        expr =
          let upd = on.value {
            Inc = _: n: { model = n + 1; };
            Add = x: n: { model = n + x; };
          };
          in { inc = (upd { Inc = null; } 5).model; add = (upd { Add = 3; } 10).model; };
        expected = { inc = 6; add = 13; };
      };
      "on-unknown-noop" = {
        expr =
          let upd = on.value { Inc = _: n: { model = n + 1; }; };
          in { model = (upd { Unknown = null; } 7).model;
               cmd   = (handle { handlers = {}; } (upd { Unknown = null; } 0).cmd).value; };
        expected = { model = 7; cmd = []; };
      };
      "on-optional-cmd" = {
        # Handlers need not return cmd; defaults to Cmd.none.
        expr =
          let upd = on.value { Inc = _: n: { model = n + 1; }; };
          in (handle { handlers = {}; } (upd { Inc = null; } 0).cmd).value;
        expected = [];
      };
    };
  };

  # ── msg ──────────────────────────────────────────────────────────────────

  msg = mk {
    doc = ''
      Build a message attrset when the tag is a runtime variable.
      Plain literals `{ Inc = null }` are identical and usually preferred.

      ```
      msg : String -> payload -> { ''${tag} = payload }
      ```
    '';
    value = tag: payload: { ${tag} = payload; };
    tests = {
      "msg-builds" = {
        expr     = { a = msg.value "Inc" null; b = msg.value "Add" 5; };
        expected = { a = { Inc = null; }; b = { Add = 5; }; };
      };
    };
  };

  # ── dispatch ─────────────────────────────────────────────────────────────

  dispatch = mk {
    doc = ''
      Inject a message into the running TEA loop from inside a Computation
      (e.g. from a Cmd, a subscription handler, or a test).  Equivalent to
      calling `update` and re-rendering, which is exactly what happens.

      ```
      dispatch : msg -> Computation null
      ```
    '';
    value = send "tea:dispatch";
    tests = {
      "dispatch-sends-to-program" = {
        expr =
          let
            prog = {
              init   = _: { model = 0; };
              update = on.value { Inc = _: n: { model = n + 1; }; };
              view   = n: { n = n; };
            };
            s0 = { model = 0; view = { n = 0; }; };
            r  = handle { handlers = mkHandlers.value prog; state = s0; }
                   (bind (dispatch.value { Inc = null; }) (_: dispatch.value { Inc = null; }));
          in r.state.model;
        expected = 2;
      };
    };
  };

  # ── getModel / getView ────────────────────────────────────────────────────

  getModel = mk {
    doc = ''
      Read the current model from within a running TEA computation.
      Useful in tests and in `scope` bodies that need to inspect state.
      With `tea.nest`, the model includes the merged models of all nested
      children under their attribute names.

      ```
      getModel : Computation model
      ```
    '';
    value = send "tea:getModel" null;
    tests = {
      "getModel-reads-model" = {
        expr =
          let
            prog = {
              init   = _: { model = 0; };
              update = on.value { Inc = _: n: { model = n + 1; }; };
              view   = n: { n = n; };
            };
            s0 = { model = 0; view = { n = 0; }; };
            r  = handle { handlers = mkHandlers.value prog; state = s0; }
                   (bind (dispatch.value { Inc = null; }) (_: getModel.value));
          in r.value;
        expected = 1;
      };
    };
  };

  getView = mk {
    doc = ''
      Read the rendered view for the current model from within a running
      TEA computation.  The view is always kept in sync with the model.
      With `tea.nest`, the view is auto-composed from view fragments and
      child views unless an explicit `view` attr overrides it.

      ```
      getView : Computation view
      ```
    '';
    value = send "tea:getView" null;
    tests = {
      "getView-reads-view" = {
        expr =
          let
            prog = {
              init   = _: { model = 7; };
              update = _: _: { model = 7; };
              view   = n: { label = "n=${toString n}"; };
            };
            s0 = { model = 7; view = { label = "n=7"; }; };
            r  = handle { handlers = mkHandlers.value prog; state = s0; } getView.value;
          in r.value.label;
        expected = "n=7";
      };
    };
  };

  # ── mkHandlers ────────────────────────────────────────────────────────────

  mkHandlers = mk {
    doc = ''
      Produce the raw `{ "tea:dispatch"; "tea:sub"; "tea:getModel"; "tea:getView" }`
      handler attrset for a TEA program, suitable for passing to `fx.handle` or
      `fx.rotate`.

      When the program declares a `handlers : model -> attrs` field, those
      handlers are installed (via `fx.rotate`) around each Cmd execution after
      dispatch, using the *updated* model.  This lets a component intercept
      algebraic effects from its own Cmds without touching the outer scope.

      For manual parent-child wiring, `fx.adaptHandlers` can embed a child's
      handler set into any parent state via a lens:

      ```nix
      # Embed a child TEA program into the parent effect scope:
      childHandlers = fx.adaptHandlers {
        get = s: s.child;             # lens into parent state
        set = s: c: s // { child = c; };
      } (tea.mkHandlers childProgram);
      ```

      Prefer `tea.nest` / `tea { … }` over manual `mkHandlers` wiring for
      typical parent-child composition — it composes init, update,
      subscriptions, view, and handlers automatically.
    '';
    value = mkHandlers_;
    tests = {
      "mkHandlers-dispatch-updates-model-and-view" = {
        expr =
          let
            prog = {
              init   = _: { model = 0; };
              update = on.value { Inc = _: n: { model = n + 1; }; };
              view   = n: { count = n; };
            };
            s0 = { model = 0; view = { count = 0; }; };
            r  = handle { handlers = mkHandlers.value prog; state = s0; }
                   (bind (dispatch.value { Inc = null; }) (_: dispatch.value { Inc = null; }));
          in { model = r.state.model; view = r.state.view.count; };
        expected = { model = 2; view = 2; };
      };
      "mkHandlers-nesting-via-adaptHandlers" = {
        # Child handlers adapt into parent state; unrelated parent key preserved.
        expr =
          let
            child = {
              init   = _: { model = 0; };
              update = on.value { Inc = _: n: { model = n + 1; }; };
              view   = n: { n = n; };
            };
            childHandlers = fx.adapt.adaptHandlers {
              get = s: s.child;
              set = s: c: s // { child = c; };
            } (mkHandlers.value child);
            s0 = { child = { model = 0; view = { n = 0; }; }; extra = "ok"; };
            r  = handle { handlers = childHandlers; state = s0; }
                   (dispatch.value { Inc = null; });
          in { model = r.state.child.model; extra = r.state.extra; };
        expected = { model = 1; extra = "ok"; };
      };
    };
  };

  # ── run ──────────────────────────────────────────────────────────────────

  run = mk {
    doc = ''
      Equivalent to `Browser.sandbox` in Elm: runs the program to completion
      and returns the final `{ model, view }`.  The init Cmd is processed
      first, then any Cmds emitted by update, until the queue is empty.

      Works with any program record, including components produced by
      `tea.nest`.  The `handlers` field (if present) is active throughout
      all Cmd processing.

      Use `scope` instead when Cmds need access to outer effects (like a
      parent's Reader or State handler).

      ```
      run : Program -> flags -> { model, view }
      ```
    '';
    value = program: flags:
      let
        s0    = normResult (program.init flags);
        state = { model = s0.model; view = program.view s0.model; };
        result = handle { handlers = mkHandlers_ program; state = state; } (processCmd s0.cmd);
      in { inherit (result.state) model view; };
    tests = {
      "run-no-cmd-with-flags" = {
        # init may omit cmd; flags are passed; view reflects model.
        expr =
          let
            prog = {
              init   = flags: { model = flags.start; };
              update = _: _: { model = 0; };
              view   = n: { count = n; };
            };
            r = run.value prog { start = 42; };
          in { model = r.model; view = r.view.count; };
        expected = { model = 42; view = 42; };
      };
      "run-cmd-from-init" = {
        expr =
          let prog = {
            init   = _: { model = 0; cmd = Cmd.value.msg { Inc = null; }; };
            update = on.value { Inc = _: n: { model = n + 1; }; };
            view   = n: { n = n; };
          };
          in (run.value prog null).model;
        expected = 1;
      };
      "run-batch-cmds" = {
        expr =
          let prog = {
            init   = _: { model = 0; cmd = Cmd.value.batch [
              (Cmd.value.msg { Inc = null; })
              (Cmd.value.msg { Inc = null; })
              (Cmd.value.msg { Add = 5; })
            ]; };
            update = on.value {
              Inc = _: n: { model = n + 1; };
              Add = x: n: { model = n + x; };
            };
            view = n: { n = n; };
          };
          in (run.value prog null).model;
        expected = 7;
      };
      "run-cmd-chain-from-update" = {
        # update emits a follow-up cmd; chaining terminates correctly.
        expr =
          let prog = {
            init   = _: { model = 0; cmd = Cmd.value.msg { Start = null; }; };
            update = on.value {
              Start  = _: n: { model = n;       cmd = Cmd.value.msg { Finish = null; }; };
              Finish = _: n: { model = n + 100; };
            };
            view = n: { n = n; };
          };
          in (run.value prog null).model;
        expected = 100;
      };
    };
  };

  # ── scope ────────────────────────────────────────────────────────────────

  scope = mk {
    doc = ''
      Equivalent to `Browser.element` / `Browser.document` in Elm: installs
      TEA handlers *around* a body computation so that Cmds can use effects
      provided by outer handlers (a parent's State, Reader, etc.).

      Any effect the program does not handle rotates outward to the surrounding
      effect scope — Cmds are not sandboxed.  Component-level `handlers` are
      still active for their own Cmds; unhandled effects rotate outward as
      usual, letting outer scopes (e.g. a parent TEA scope) catch them.

      ```
      scope : Program -> flags -> Computation a -> Computation { model, view, value }
      ```
    '';
    value = program: flags: body:
      let
        s0    = normResult (program.init flags);
        state = { model = s0.model; view = program.view s0.model; };
      in
        bind
          (rotate { handlers = mkHandlers_ program; state = state; }
            (bind (processCmd s0.cmd) (_: body)))
          ({ value, state }: pure { inherit value; inherit (state) model view; });
    tests = {
      "scope-dispatch-and-model" = {
        expr =
          let
            prog = {
              init   = _: { model = 10; };
              update = on.value { Add5 = _: n: { model = n + 5; }; };
              view   = n: { n = n; };
            };
            result = handle { handlers = {}; }
              (scope.value prog null (dispatch.value { Add5 = null; }));
          in result.value.model;
        expected = 15;
      };
      "scope-outer-effect-rotates" = {
        expr =
          let
            prog = {
              init   = _: { model = 0; };
              update = _: n: { model = n; };
              view   = n: { n = n; };
            };
            result = handle {
              handlers.outer = { param, state }: { resume = param * 2; inherit state; };
            } (scope.value prog null (send "outer" 7));
          in result.value.value;
        expected = 14;
      };
      "scope-processes-init-cmd" = {
        expr =
          let
            prog = {
              init   = _: { model = 0; cmd = Cmd.value.msg { Inc = null; }; };
              update = on.value { Inc = _: n: { model = n + 1; }; };
              view   = n: { n = n; };
            };
            result = handle { handlers = {}; }
              (scope.value prog null (pure "done"));
          in result.value.model;
        expected = 1;
      };
    };
  };

  # ── nestValue (recursive impl behind nest / tea __functor) ───────────────

  # Standard TEA field names excluded from auto-detection.
  teaReserved = [ "init" "update" "subscriptions" "view" "handlers" ];

  # Recursively build a fully child-aware TEA component from an attr-set.
  # Classification of extra (non-reserved) attrs:
  #   function   → view fragment  (called with the full composed model)
  #   attrset    → child component (recursively nested via nestValue)
  # Everything else is ignored.
  nestValue = attrs:
    let
      extras       = lib.filterAttrs (k: _: !(builtins.elem k teaReserved)) attrs;
      viewFragments = lib.filterAttrs (_: builtins.isFunction) extras;
      rawChildren   = lib.filterAttrs (_: builtins.isAttrs)   extras;

      # Recursively nest every child so they all expose init/update/subscriptions/view.
      children  = lib.mapAttrs (_: nestValue) rawChildren;
      childNames = builtins.attrNames children;

      # User-provided TEA fields with sensible defaults.
      userInit     = attrs.init          or (_: { model = {}; });
      userUpdate   = attrs.update        or (_: m: { model = m; });
      userSubs     = attrs.subscriptions or (_: []);
      userHandlersF = attrs.handlers    or (_: {});
      # An explicit `view` attr overrides auto-composition from fragments/children.
      userView     = attrs.view or null;

      # ── Composed init ───────────────────────────────────────────────────
      # Initialises self, then each child (same flags); merges models and
      # batches all init-time Cmds, wrapping each child's Cmds appropriately.
      composedInit = flags:
        let
          selfResult   = normResult (userInit flags);
          childResults = lib.mapAttrs (name: child:
            let r = normResult (child.init flags);
            in { model = r.model;
                 cmd   = Cmd.value.map (m: { ${name} = m; }) r.cmd; }
          ) children;
          childModels = lib.mapAttrs (_: r: r.model) childResults;
          childCmds   = builtins.attrValues (lib.mapAttrs (_: r: r.cmd) childResults);
          allCmd        = Cmd.value.batch ([ selfResult.cmd ] ++ childCmds);
          composedModel =
            if childNames == []
            then selfResult.model
            else selfResult.model // childModels;
        in { model = composedModel; cmd = allCmd; };

      # ── Composed update ─────────────────────────────────────────────────
      # Messages whose tag matches a child name are routed to that child;
      # everything else goes to the user's update.  After a user-update the
      # child sub-models are re-merged so they can never be accidentally
      # clobbered by a parent handler that returns a fresh attrset.
      composedUpdate = msg: model:
        let
          tag     = tagOf msg;
          payload = payloadOf msg;
        in
        if children ? ${tag}
        then
          let
            child       = children.${tag};
            childResult = normResult (child.update payload model.${tag});
            mappedCmd   = Cmd.value.map (m: { ${tag} = m; }) childResult.cmd;
          in { model = model // { ${tag} = childResult.model; }; cmd = mappedCmd; }
        else
          let userResult = normResult (userUpdate msg model);
          in
          if childNames == []
          then userResult
          else
            let childModels = lib.filterAttrs (k: _: builtins.hasAttr k children) model;
            in { model = userResult.model // childModels; cmd = userResult.cmd; };

      # ── Composed subscriptions ──────────────────────────────────────────
      # Aggregates own subs with each child's subs, wrapping child subs so
      # they produce `{ childName = childMsg }` messages when fired.
      composedSubs = model:
        let
          selfSubs     = userSubs model;
          childSubsList = builtins.concatLists (map (name:
            map (Sub.value.map (m: { ${name} = m; }))
                ((children.${name}).subscriptions (model.${name} or {}))
          ) childNames);
        in selfSubs ++ childSubsList;

      # ── Composed view ───────────────────────────────────────────────────
      # Auto-view: every fragment called with the full model, each child's
      # view called with its slice of the model, merged into one attrset.
      # An explicit `view` attr overrides this entirely.
      autoView = model:
        (lib.mapAttrs (_: frag: frag model) viewFragments) //
        (lib.mapAttrs (name: child: child.view (model.${name} or {})) children);

      composedView = if userView != null then userView else autoView;

      # ── Composed handlers ───────────────────────────────────────────────
      # Merges the user's own handlers with each child's composed handlers,
      # each called with its own model slice.  Children can expose effect
      # handlers that bubble up automatically to all ancestors.
      composedHandlers = model:
        let
          selfHandlers  = userHandlersF model;
          childHandlers = builtins.foldl' (acc: name:
            let h = ((children.${name}).handlers or (_: {})) (model.${name} or {});
            in acc // h
          ) {} childNames;
        in selfHandlers // childHandlers;
    in {
      init          = composedInit;
      update        = composedUpdate;
      subscriptions = composedSubs;
      view          = composedView;
      handlers      = composedHandlers;
    };

  nest = mk {
    doc = ''
      `tea.nest` (callable as `tea { … }` via `__functor`) builds a
      fully child-aware TEA component from a plain attribute set.
      It is the primary composition API — use it instead of manually
      wiring `mkHandlers` / `fx.adaptHandlers` for typical trees.

      ## Reserved attribute names

      | Name            | Type                          | Semantics |
      |-----------------|-------------------------------|-----------|
      | `init`          | `flags -> { model, cmd? }`    | Standard TEA init |
      | `update`        | `msg -> model -> { model, cmd? }` | Standard TEA update |
      | `subscriptions` | `model -> [Sub]`              | Standard TEA subs |
      | `view`          | `model -> view`               | Explicit view (overrides auto-compose) |
      | `handlers`      | `model -> { effectName = handler }` | Per-component effect scope |

      ## Extra attributes — auto-classified

      | Value type | Role |
      |------------|------|
      | function   | **view fragment** — called with the full composed model; key becomes a slot in the auto-composed view |
      | attrset    | **child component** — recursively nested via `nestValue`; child messages are wrapped as `{ childName = childMsg }` |
      | other      | ignored |

      ## What is composed automatically

      * **model** — child init-models are merged into the parent model under
        the child's attribute name.  After every parent-level update, child
        sub-models are re-merged so they cannot be accidentally clobbered.
      * **update** — messages tagged with a child's name are routed to that
        child; all other messages go to the user's `update`.
      * **subscriptions** — child subs are mapped through `{ childName = … }`
        and concatenated with the parent's own subs.
      * **view** — auto-composed from view fragments (each called with the
        full model) and each child's `view` (called with the child's model
        slice).  Supplying an explicit `view` attr overrides this entirely.
      * **handlers** — the user's `handlers model` is merged with every
        child's `handlers` (called with the child's model slice).  This
        means any child can expose an algebraic effect handler that is
        automatically available to *all* Cmds in the composed component,
        including the parent's own Cmds and sibling Cmds.

      ## Example

      ```nix
      let app = tea {
        init   = _: { model = { n = 0; }; };
        update = tea.on {
          Inc = _: m: { model = m // { n = m.n + 1; }; };
          # Cmd sends "log"; logger child's handler catches it:
          Log = _: m: { model = m; cmd = send "log" "incremented"; };
        };
        label = m: "count: ''${toString m.n}";   # view fragment

        # Nested child exposes a "log" handler from its own model.
        logger = tea {
          init     = _: { model = []; };
          update   = tea.on { Append = s: ms: { model = ms ++ [ s ]; }; };
          view     = ms: { lines = ms; };
          handlers = _: {
            log = { param, state, ... }:
              { resume = pure null; inherit state; };
          };
        };
      };
      in tea.run app null
      # => {
      #      model = { n = 0; logger = []; };
      #      view  = { label = "count: 0"; logger = { lines = []; }; };
      #    }
      ```
    '';
    value = nestValue;
    tests = {

      "nest-view-fragments" = {
        # Functions in extras become view fragments keyed by their attr name.
        expr =
          let
            comp = nestValue {
              init   = _: { model = 10; };
              update = _: m: { model = m; };
              label   = n: "val:${toString n}";
              doubled = n: n * 2;
            };
          in (run.value comp null).view;
        expected = { label = "val:10"; doubled = 20; };
      };

      "nest-child-model-in-parent" = {
        # Child's init model is stored under the child's attr name.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { x = 1; }; };
              update = _: m: { model = m; };
              counter = {
                init   = _: { model = 42; };
                update = _: m: { model = m; };
                view   = m: { n = m; };
              };
            };
          in (run.value comp null).model;
        expected = { x = 1; counter = 42; };
      };

      "nest-child-message-routing" = {
        # { childName = childMsg } is routed to the child's update.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { x = 0; }; };
              update = on.value { Inc = _: m: { model = m // { x = m.x + 1; }; }; };
              counter = {
                init   = _: { model = 0; };
                update = on.value { Add = n: c: { model = c + n; }; };
                view   = c: c;
              };
            };
            initResult = normResult (comp.init null);
            s0 = { model = initResult.model; view = comp.view initResult.model; };
            r  = handle { handlers = mkHandlers.value comp; state = s0; }
                   (bind (dispatch.value { counter = { Add = 5; }; })
                     (_: dispatch.value { Inc = null; }));
          in r.state.model;
        expected = { x = 1; counter = 5; };
      };

      "nest-child-model-preserved-on-parent-msg" = {
        # nest re-merges child sub-models after a parent update so they
        # cannot be accidentally clobbered even when the handler returns
        # a fresh attrset without child keys.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { x = 0; }; };
              # Intentionally returns a fresh record without the `kid` key.
              update = on.value { Reset = _: _: { model = { x = 0; }; }; };
              kid = {
                init   = _: { model = 99; };
                update = _: m: { model = m; };
                view   = m: m;
              };
            };
            initResult = normResult (comp.init null);
            s0 = { model = initResult.model; view = comp.view initResult.model; };
            r  = handle { handlers = mkHandlers.value comp; state = s0; }
                   (dispatch.value { Reset = null; });
          in r.state.model;
        expected = { x = 0; kid = 99; };
      };

      "nest-child-subscriptions-aggregated" = {
        # Child subscriptions are mapped through { childName = … } and
        # firing the event updates the child model.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { x = 0; }; };
              update = _: m: { model = m; };
              counter = {
                init          = _: { model = 0; };
                update        = on.value { Add = n: c: { model = c + n; }; };
                subscriptions = _: [{ tick = _: { Add = 1; }; }];
                view          = c: c;
              };
            };
            initResult = normResult (comp.init null);
            s0 = { model = initResult.model; view = comp.view initResult.model; };
            r  = handle { handlers = mkHandlers.value comp; state = s0; }
                   (Sub.value.fire { tick = null; });
          in r.state.model.counter;
        expected = 1;
      };

      "nest-recursive-children" = {
        # Messages can be nested two levels deep: { child = { gc = childMsg } }.
        expr =
          let
            grandchild = {
              init   = _: { model = 0; };
              update = on.value { Bump = _: n: { model = n + 10; }; };
              view   = n: { val = n; };
            };
            child = nestValue {
              init   = _: { model = { label = "c"; }; };
              update = _: m: { model = m; };
              gc     = grandchild;
            };
            parent = nestValue {
              init   = _: { model = { top = true; }; };
              update = _: m: { model = m; };
              child  = child;
            };
            initResult = normResult (parent.init null);
            s0 = { model = initResult.model; view = parent.view initResult.model; };
            r  = handle { handlers = mkHandlers.value parent; state = s0; }
                   (dispatch.value { child = { gc = { Bump = null; }; }; });
          in r.state.model.child.gc;
        expected = 10;
      };

      "nest-child-view-in-composed-view" = {
        # Each child's view is included in the parent's auto-composed view
        # under the child's attr name.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { n = 3; }; };
              update = _: m: { model = m; };
              label  = m: "n=${toString m.n}";
              badge  = {
                init   = _: { model = true; };
                update = _: m: { model = m; };
                view   = b: { active = b; };
              };
            };
          in (run.value comp null).view;
        expected = { label = "n=3"; badge = { active = true; }; };
      };

      "nest-explicit-view-overrides" = {
        # When user supplies an explicit `view` attr it overrides the
        # auto-composed view; view fragments are ignored.
        expr =
          let
            comp = nestValue {
              init   = _: { model = 4; };
              update = _: m: { model = m; };
              view   = n: { explicit = n * 3; };
              extra  = n: n + 1;   # would be a fragment, but view is explicit
            };
          in (run.value comp null).view;
        expected = { explicit = 12; };
      };

      "nest-init-cmds-from-children" = {
        # Cmds emitted by child init are processed and wrapped correctly.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { x = 0; }; };
              update = on.value {
                Inc    = _: m: { model = m // { x = m.x + 1; }; };
                # Child wraps its message: { counter = { Add = … } }
                counter = m: model:
                  let r = on.value { Add = n: c: { model = c + n; }; } m model.counter;
                  in { model = model // { counter = r.model; }; };
              };
              counter = {
                init   = _: { model = 0;
                              cmd  = Cmd.value.msg { Add = 10; }; };
                update = on.value { Add = n: c: { model = c + n; }; };
                view   = c: c;
              };
            };
          in (run.value comp null).model.counter;
        expected = 10;
      };

      # ── handlers field ────────────────────────────────────────────────────

      "handlers-catches-effect-from-cmd" = {
        # A component's `handlers` field intercepts effects sent from Cmds.
        expr =
          let
            prog = nestValue {
              init   = _: { model = 0; };
              update = on.value {
                Fetch = _: _: {
                  model = 0;
                  cmd = bind (send "myEff" null) (v: pure [{ Got = v; }]);
                };
                Got = v: _: { model = v; };
              };
              view     = n: n;
              handlers = _: {
                myEff = { state, ... }: { resume = pure 42; inherit state; };
              };
            };
            s0 = { model = 0; view = 0; };
            r  = handle { handlers = mkHandlers.value prog; state = s0; }
                   (dispatch.value { Fetch = null; });
          in r.state.model;
        expected = 42;
      };

      "handlers-dynamic-based-on-model" = {
        # Handlers are re-evaluated from the updated model after each dispatch,
        # so they can activate or deactivate based on current state.
        expr =
          let
            prog = nestValue {
              init   = _: { model = { n = 0; factor = 3; }; };
              update = on.value {
                Fetch     = _: m: {
                  model = m;
                  cmd = bind (send "myEff" null) (v: pure [{ Got = v; }]);
                };
                Got       = v: m: { model = m // { n = v; }; };
                SetFactor = f: m: { model = m // { factor = f; }; };
              };
              view     = m: m;
              handlers = m: {
                myEff = { state, ... }: { resume = pure m.factor; inherit state; };
              };
            };
            s0 = { model = { n = 0; factor = 3; }; view = { n = 0; factor = 3; }; };
            r  = handle { handlers = mkHandlers.value prog; state = s0; }
                   (bind (dispatch.value { SetFactor = 7; }) (_:
                     dispatch.value { Fetch = null; }));
          in r.state.model.n;
        expected = 7;
      };

      "handlers-child-effect-caught-by-parent" = {
        # Child Cmd sends an effect; parent's `handlers` catches it.
        # The effect result is used to construct a message routed back via the child.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { x = 0; }; };
              update = _: m: { model = m; };
              # Parent provides "fetch" handler visible to all child Cmds.
              handlers = _: {
                fetch = { state, ... }: { resume = pure 55; inherit state; };
              };
              child = {
                init   = _: { model = 0; };
                update = on.value {
                  Fetch = _: c: {
                    model = c;
                    # Cmd sends "fetch"; parent catches it; result routed back as Set.
                    cmd = bind (send "fetch" null) (v: pure [{ Set = v; }]);
                  };
                  Set = v: _: { model = v; };
                };
                view = c: c;
              };
            };
            initResult = normResult (comp.init null);
            s0 = { model = initResult.model; view = comp.view initResult.model; };
            r  = handle { handlers = mkHandlers.value comp; state = s0; }
                   (dispatch.value { child = { Fetch = null; }; });
          in r.state.model.child;
        expected = 55;
      };

      "handlers-child-exposes-to-parent" = {
        # A child's `handlers` field bubbles up via composedHandlers so it
        # is active during ALL cmd processing in the composed component.
        expr =
          let
            comp = nestValue {
              init   = _: { model = { n = 0; }; };
              update = on.value {
                Compute = _: m: {
                  model = m;
                  # Parent's own Cmd also benefits from child-exposed handlers.
                  cmd = bind (send "childSvc" null) (v: pure [{ Got = v; }]);
                };
                Got = v: m: { model = m // { n = v; }; };
              };
              view = m: m;
              svc = {
                init    = _: { model = 100; };
                update  = _: m: { model = m; };
                view    = m: m;
                # Child exposes a service effect using its own model as the value.
                handlers = m: {
                  childSvc = { state, ... }: { resume = pure m; inherit state; };
                };
              };
            };
            s0 = { model = { n = 0; svc = 100; }; view = { n = 0; svc = 100; }; };
            r  = handle { handlers = mkHandlers.value comp; state = s0; }
                   (dispatch.value { Compute = null; });
          in r.state.model.n;
        expected = 100;
      };

    };
  };

in mk {
  doc = ''
    The Elm Architecture (TEA) for nix-effects (Czaplicki 2012, Evans 2019).

    Elm's Model-View-Update loop maps directly to nix-effects.  A TEA program
    is a plain record; `tea.run` drives it to completion:

    ```nix
    let counter = {
      init   = _: { model = 0; };             # flags -> { model, cmd? }
      update = tea.on {
        Inc = _: n: { model = n + 1; };        # msg -> model -> { model, cmd? }
        Add = x: n: { model = n + x; };
      };
      view          = model: { count = model; };  # model -> View
      subscriptions = _: [{ clock = _: { Inc = null; }; }];  # model -> [Sub]
    };
    in tea.run counter null
    # => { model = 0; view = { count = 0; }; }
    ```

    ## Uniform single-key attrsets

    Messages, subscriptions, and fired events all use the same `{ Name = value }`
    shape.  No separate type constructors needed:

    ```
    message   | Examples:   { Inc = null }          { Add = 5 }
    sub       | Examples:   { clock = _: msg }      { key = k: { Key = k; } }
    Sub.fire  | Examples:   { clock = null }        { key = "Enter" }
    ```

    ## cmd is optional everywhere

    Handlers that have no side effects simply omit `cmd`; `Cmd.none` is implied.

    ## handlers — per-component algebraic effect scope

    A program may declare `handlers : model -> { effectName = handler }` to
    intercept algebraic effects emitted from its Cmds.  The handler set is
    re-derived from the *post-update* model after every dispatch, enabling
    components to activate or deactivate handlers dynamically:

    ```nix
    handlers = model: lib.optionalAttrs model.online {
      fetch = { param, state, ... }:
        { resume = httpGet param; inherit state; };
    };
    ```

    Effects not caught by `handlers` rotate outward to the surrounding scope
    as usual, so components remain composable.

    ## nest / tea { … } — automatic child-aware composition

    `tea { … }` (or `tea.nest { … }`) builds a complete component from a
    plain attribute set.  Function-valued extra attrs become view fragments;
    attrset-valued extra attrs become nested child components.  All five
    fields — init, update, subscriptions, view, handlers — are composed
    recursively with no manual wiring:

    ```nix
    let app = tea {
      init   = _: { model = { n = 0; }; };
      update = tea.on { Inc = _: m: { model = m // { n = m.n + 1; }; }; };
      label  = m: "count: ''${toString m.n}";   # view fragment

      badge = tea {                              # nested child
        init     = _: { model = false; };
        update   = tea.on { Toggle = _: b: { model = !b; }; };
        icon     = b: if b then "on" else "off";
        handlers = _: { myEff = { state, ... }: { resume = pure 42; inherit state; }; };
      };
    };
    in tea.run app null
    ```

    Child `handlers` bubble up automatically, so `badge`'s `myEff` handler
    is active for *all* Cmds in the composed program — including the parent's.

    ## Manual parent-child composition

    For cases where `tea.nest` is not flexible enough, `mkHandlers` exposes
    the raw handler attrset.  Use `fx.adaptHandlers` with a lens to embed
    a child's handler set into any parent state:

    ```nix
    childHandlers = fx.adaptHandlers {
      get = s: s.child;
      set = s: c: s // { child = c; };
    } (tea.mkHandlers childProgram);
    ```
  '';
  value = {
    inherit Cmd Sub on msg dispatch getModel getView run scope mkHandlers nest;
    __functor = _: nest.value;
  };
  tests = {
    # ── Subscriptions ─────────────────────────────────────────────────────────

    "sub-fires-on-match" = {
      expr =
        let
          prog = {
            init   = _: { model = 0; };
            update = on.value { Tick = _: n: { model = n + 1; }; };
            view   = n: { n = n; };
            subscriptions = _: [{ tick = _: { Tick = null; }; }];
          };
          s0 = { model = 0; view = { n = 0; }; };
          r  = handle { handlers = mkHandlers.value prog; state = s0; }
                 (Sub.value.fire { tick = null; });
        in r.state.model;
      expected = 1;
    };

    "sub-silent-on-no-match" = {
      expr =
        let
          prog = {
            init   = _: { model = 5; };
            update = on.value { Tick = _: n: { model = n + 1; }; };
            view   = n: { n = n; };
            subscriptions = _: [{ tick = _: { Tick = null; }; }];
          };
          s0 = { model = 5; view = { n = 5; }; };
          r  = handle { handlers = mkHandlers.value prog; state = s0; }
                 (Sub.value.fire { key = "a"; });
        in r.state.model;
      expected = 5;    # unmatched event → no change
    };

    "sub-toMsg-receives-param" = {
      expr =
        let
          prog = {
            init   = _: { model = ""; };
            update = on.value { Key = k: _: { model = k; }; };
            view   = m: { text = m; };
            subscriptions = _: [{ key = k: { Key = k; }; }];
          };
          s0 = { model = ""; view = { text = ""; }; };
          r  = handle { handlers = mkHandlers.value prog; state = s0; }
                 (Sub.value.fire { key = "Enter"; });
        in r.state.model;
      expected = "Enter";
    };

    "sub-dynamic-follows-model" = {
      # Subscriptions re-read after each update: tick ignored after Stop.
      expr =
        let
          prog = {
            init   = _: { model = { count = 0; active = true; }; };
            update = on.value {
              Tick = _: m: { model = m // { count = m.count + 1; }; };
              Stop = _: m: { model = m // { active = false; }; };
            };
            view   = m: m;
            subscriptions = m:
              if m.active then [{ tick = _: { Tick = null; }; }] else [];
          };
          s0   = { model = { count = 0; active = true; }; view = { count = 0; active = true; }; };
          comp =
            bind (Sub.value.fire { tick = null; }) (_:    # count=1, still active
            bind (dispatch.value { Stop = null; }) (_: # deactivate
            bind (Sub.value.fire { tick = null; }) (_:    # ignored (unsubscribed)
            getModel.value)));
          r = handle { handlers = mkHandlers.value prog; state = s0; } comp;
        in r.value.count;
      expected = 1;
    };

    "sub-broadcast" = {
      # A single Sub.fire reaches ALL matching subscriptions.
      expr =
        let
          prog = {
            init   = _: { model = 0; };
            update = on.value {
              A = _: n: { model = n + 1;  };
              B = _: n: { model = n + 10; };
            };
            view   = n: { n = n; };
            subscriptions = _: [
              { clock = _: { A = null; }; }
              { clock = _: { B = null; }; }
            ];
          };
          s0 = { model = 0; view = { n = 0; }; };
          r  = handle { handlers = mkHandlers.value prog; state = s0; }
                 (Sub.value.fire { clock = null; });
        in r.state.model;
      expected = 11;    # A (+1) and B (+10) both fired
    };

    "sub-parent-aggregates-children" = {
      # Parent aggregates two children's "clock" subs via Sub.map.
      expr =
        let
          child = {
            update = on.value { Tick = _: n: { model = n + 1; }; };
            subscriptions = _: [{ clock = _: { Tick = null; }; }];
          };
          parent = {
            init   = _: { model = { a = 0; b = 0; }; };
            update = on.value {
              ForA = m: model: let r = child.update m model.a; in { model = model // { a = r.model; }; };
              ForB = m: model: let r = child.update m model.b; in { model = model // { b = r.model; }; };
            };
            view   = m: m;
            subscriptions = m:
              (map (Sub.value.map (m: { ForA = m; })) (child.subscriptions m.a)) ++
              (map (Sub.value.map (m: { ForB = m; })) (child.subscriptions m.b));
          };
          s0 = { model = { a = 0; b = 0; }; view = { a = 0; b = 0; }; };
          r  = handle { handlers = mkHandlers.value parent; state = s0; }
                 (Sub.value.fire { clock = null; });
        in r.state.model;
      expected = { a = 1; b = 1; };
    };

    # ── Parent-child communication ─────────────────────────────────────────────

    "parent-drives-child-via-cmd" = {
      # Parent sends three Inc messages to child via init Cmd batch.
      expr =
        let
          child = {
            update = on.value { Inc = _: n: { model = n + 1; }; };
          };
          parent = {
            init   = _: { model = { child = 0; }; cmd = Cmd.value.batch [
              (Cmd.value.msg { ChildMsg = { Inc = null; }; })
              (Cmd.value.msg { ChildMsg = { Inc = null; }; })
              (Cmd.value.msg { ChildMsg = { Inc = null; }; })
            ]; };
            update = on.value {
              ChildMsg = m: model:
                let r = child.update m model.child;
                in { model = model // { child = r.model; }; };
            };
            view = m: m;
          };
        in (run.value parent null).model.child;
      expected = 3;
    };

    "child-notifies-parent-via-cmd-map" = {
      # Child emits { Done = null } at threshold; parent maps it via Cmd.map.
      expr =
        let
          child = {
            update = on.value {
              Inc = _: n:
                let newN = n + 1;
                in { model = newN; cmd = if newN >= 3 then Cmd.value.msg { Done = null; } else Cmd.value.none; };
            };
          };
          parent = {
            init   = _: { model = { child = 0; reached = false; }; cmd = Cmd.value.batch [
              (Cmd.value.msg { ChildMsg = { Inc = null; }; })
              (Cmd.value.msg { ChildMsg = { Inc = null; }; })
              (Cmd.value.msg { ChildMsg = { Inc = null; }; })
            ]; };
            update = on.value {
              ChildMsg = m: model:
                let r = child.update m model.child;
                in { model = model // { child = r.model; };
                     cmd   = Cmd.value.map (cm: { FromChild = cm; }) r.cmd; };
              FromChild = _: model: { model = model // { reached = true; }; };
            };
            view = m: m;
          };
        in (run.value parent null).model.reached;
      expected = true;
    };

    "two-children-independent-state" = {
      # Children A and B accumulate independently; no cross-contamination.
      expr =
        let
          child  = { update = on.value { Inc = _: n: { model = n + 1; }; }; };
          parent = {
            init   = _: { model = { a = 0; b = 0; }; cmd = Cmd.value.batch [
              (Cmd.value.msg { ForA = { Inc = null; }; })
              (Cmd.value.msg { ForA = { Inc = null; }; })
              (Cmd.value.msg { ForB = { Inc = null; }; })
              (Cmd.value.msg { ForA = { Inc = null; }; })
            ]; };
            update = on.value {
              ForA = m: model: let r = child.update m model.a; in { model = model // { a = r.model; }; };
              ForB = m: model: let r = child.update m model.b; in { model = model // { b = r.model; }; };
            };
            view = m: m;
          };
        in (run.value parent null).model;
      expected = { a = 3; b = 1; };
    };

    # ── nest / tea { … } functor ──────────────────────────────────────────

    "nest-functor-tea-call" = {
      # tea { … } is syntactic sugar for nest.value via __functor.
      # The result is a proper TEA component usable with run.
      expr =
        let
          comp = nestValue {
            init   = _: { model = { n = 0; }; };
            update = on.value { Inc = _: m: { model = m // { n = m.n + 1; }; }; };
            label  = m: "n=${toString m.n}";
            badge  = {
              init   = _: { model = false; };
              update = on.value { Toggle = _: b: { model = !b; }; };
              icon   = b: if b then "on" else "off";
            };
          };
          r = run.value comp null;
        in { model = r.model; view = r.view; };
      expected = {
        model = { n = 0; badge = false; };
        view  = { label = "n=0"; badge = { icon = "off"; }; };
      };
    };
  };
}
