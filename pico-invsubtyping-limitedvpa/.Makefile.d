LibTactics.vo LibTactics.glob LibTactics.v.beautified LibTactics.required_vo: LibTactics.v 
LibTactics.vos LibTactics.vok LibTactics.required_vos: LibTactics.v 
Tactics.vo Tactics.glob Tactics.v.beautified Tactics.required_vo: Tactics.v LibTactics.vo
Tactics.vos Tactics.vok Tactics.required_vos: Tactics.v LibTactics.vos
Syntax.vo Syntax.glob Syntax.v.beautified Syntax.required_vo: Syntax.v 
Syntax.vos Syntax.vok Syntax.required_vos: Syntax.v 
Notations.vo Notations.glob Notations.v.beautified Notations.required_vo: Notations.v 
Notations.vos Notations.vok Notations.required_vos: Notations.v 
Helpers.vo Helpers.glob Helpers.v.beautified Helpers.required_vo: Helpers.v Syntax.vo Notations.vo LibTactics.vo Tactics.vo
Helpers.vos Helpers.vok Helpers.required_vos: Helpers.v Syntax.vos Notations.vos LibTactics.vos Tactics.vos
ViewpointAdaptation.vo ViewpointAdaptation.glob ViewpointAdaptation.v.beautified ViewpointAdaptation.required_vo: ViewpointAdaptation.v Syntax.vo
ViewpointAdaptation.vos ViewpointAdaptation.vok ViewpointAdaptation.required_vos: ViewpointAdaptation.v Syntax.vos
Subtyping.vo Subtyping.glob Subtyping.v.beautified Subtyping.required_vo: Subtyping.v Syntax.vo Notations.vo LibTactics.vo Tactics.vo Helpers.vo
Subtyping.vos Subtyping.vok Subtyping.required_vos: Subtyping.v Syntax.vos Notations.vos LibTactics.vos Tactics.vos Helpers.vos
Typing.vo Typing.glob Typing.v.beautified Typing.required_vo: Typing.v Syntax.vo Subtyping.vo ViewpointAdaptation.vo Helpers.vo
Typing.vos Typing.vok Typing.required_vos: Typing.v Syntax.vos Subtyping.vos ViewpointAdaptation.vos Helpers.vos
Bigstep.vo Bigstep.glob Bigstep.v.beautified Bigstep.required_vo: Bigstep.v Syntax.vo Typing.vo Subtyping.vo ViewpointAdaptation.vo Helpers.vo
Bigstep.vos Bigstep.vok Bigstep.required_vos: Bigstep.v Syntax.vos Typing.vos Subtyping.vos ViewpointAdaptation.vos Helpers.vos
Properties.vo Properties.glob Properties.v.beautified Properties.required_vo: Properties.v Syntax.vo Notations.vo Helpers.vo Typing.vo Subtyping.vo Bigstep.vo ViewpointAdaptation.vo
Properties.vos Properties.vok Properties.required_vos: Properties.v Syntax.vos Notations.vos Helpers.vos Typing.vos Subtyping.vos Bigstep.vos ViewpointAdaptation.vos
Main.vo Main.glob Main.v.beautified Main.required_vo: Main.v 
Main.vos Main.vok Main.required_vos: Main.v 
