# Standard Delay Format (SDF)
## A.1 Formal syntax definition
&nbsp;&nbsp;&nbsp;&nbsp;[The](#The) [formal](#formal) [syntax](#syntax) [of](#of) [SDF](#SDF) [is](#is) [described](#described) [using](#using) [Backus](#Backus)`-`[Naur](#Naur) `(`[BNF](#BNF)`).`
&nbsp;&nbsp;&nbsp;&nbsp;[Lexical](#Lexical) [elements](#elements) [are](#are) [shown](#shown) [italicized](#italicized)`.` [All](#All) [leaf](#leaf) [characters](#characters) [are](#are) [shown](#shown) [in](#in) [bold](#bold)`.` [Keywords](#Keywords) [are](#are) [shown](#shown) [in](#in) [uppercase](#uppercase) [bold](#bold) `(`[for](#for) [example](#example)`,` [IOPATH](#IOPATH)`)` [for](#for) [easy](#easy) [identification](#identification)`,` [but](#but) [are](#are) [case](#case) [insensitive](#insensitive)`.`
### A.1.1 SDF delay file and header
<a name="delay_file"></a>delay\_file ::= `(` [DELAYFILE](#DELAYFILE) [sdf_header](#sdf_header) [cell](#cell) \{ [cell](#cell) } `)`
<a name="sdf_header"></a>sdf\_header ::=
&nbsp;&nbsp;&nbsp;&nbsp;[sdf_version](#sdf_version) \[ [design_name](#design_name) ] \[ [date](#date) ] \[ [vendor](#vendor) ] \[ [program_name](#program_name) ] \[ [program_version](#program_version) ] \[[hierarchy_divider](#hierarchy_divider) ] \[ [voltage](#voltage) ] \[ [process](#process) ] \[[temperature](#temperature) ] \[ [time_scale](#time_scale) ]
<a name="sdf_version"></a>sdf\_version ::= `(` [SDFVERSION](#SDFVERSION) [qstring](#qstring) `)`
<a name="design_name"></a>design\_name ::= `(` [DESIGN](#DESIGN) [qstring](#qstring) `)`
<a name="date"></a>date ::= `(` [DATE](#DATE) [qstring](#qstring) `)`
<a name="vendor"></a>vendor ::= `(` [VENDOR](#VENDOR) [qstring](#qstring) `)`
<a name="program_name"></a>program\_name ::= `(` [PROGRAM](#PROGRAM) [qstring](#qstring) `)`
<a name="program_version"></a>program\_version ::= `(` [VERSION](#VERSION) [qstring](#qstring) `)`
<a name="hierarchy_divider"></a>hierarchy\_divider ::= `(` [DIVIDER](#DIVIDER) [hchar](#hchar) `)`
<a name="voltage"></a>voltage ::= `(` [VOLTAGE](#VOLTAGE) [rtriple](#rtriple) `)` \| `(` [VOLTAGE](#VOLTAGE) [signed_real_number](#signed_real_number) `)`
<a name="process"></a>process ::= `(` [PROCESS](#PROCESS) [qstring](#qstring) `)`
<a name="temperature"></a>temperature ::= `(` [TEMPERATURE](#TEMPERATURE) [rtriple](#rtriple) `)` \| `(` [TEMPERATURE](#TEMPERATURE) [signed_real_number](#signed_real_number) `)`
<a name="time_scale"></a>time\_scale ::= `(` [TIMESCALE](#TIMESCALE) [timescale_number](#timescale_number) [timescale_unit](#timescale_unit) `)`
<a name="timescale_number"></a>timescale\_number ::= [1](#1) \| [10](#10) \| [100](#100) \| [1](#1)`.`[0](#0) \| [10](#10)`.`[0](#0) \| [100](#100)`.`[0](#0)
<a name="timescale_unit"></a>timescale\_unit ::= [s](#s) \| [ms](#ms) \| [us](#us) \| [ns](#ns) \| [ps](#ps) \| [fs](#fs)
### A.1.2 Cells
<a name="cell"></a>cell ::= `(` [CELL](#CELL) [celltype](#celltype) [cell_instance](#cell_instance) \{ [timing_spec](#timing_spec) } `)`
<a name="celltype"></a>celltype ::= `(` [CELLTYPE](#CELLTYPE) [qstring](#qstring) `)`
<a name="cell_instance"></a>cell\_instance ::= `(` [INSTANCE](#INSTANCE) \[ [hierarchical_identifier](#hierarchical_identifier) ] `)` \| `(` [INSTANCE](#INSTANCE) `*` `)`
### A.1.3 Timing specifications
<a name="timing_spec"></a>timing\_spec ::= [del_spec](#del_spec) \| [tc_spec](#tc_spec) \| [lbl_spec](#lbl_spec) \| [te_spec](#te_spec)
<a name="del_spec"></a>del\_spec ::= `(` [DELAY](#DELAY) [deltype](#deltype) \{ [deltype](#deltype) } `)`
<a name="tc_spec"></a>tc\_spec ::= `(` [TIMINGCHECK](#TIMINGCHECK) [tchk_def](#tchk_def) \{ [tchk_def](#tchk_def) } `)`
<a name="te_spec"></a>te\_spec ::= `(` [TIMINGENV](#TIMINGENV) [te_def](#te_def) \{ [te_def](#te_def) } `)`
<a name="lbl_spec"></a>lbl\_spec ::= `(` [LABEL](#LABEL) [lbl_type](#lbl_type) \{ [lbl_type](#lbl_type) } `)`
<a name="deltype"></a>deltype ::= \| [absolute_deltype](#absolute_deltype) \| [increment_deltype](#increment_deltype) \| [pathpulse_deltype](#pathpulse_deltype) \| [pathpulsepercent_deltype](#pathpulsepercent_deltype)
<a name="pathpulse_deltype"></a>pathpulse\_deltype ::= `(` [PATHPULSE](#PATHPULSE) \[ [input_output_path](#input_output_path) ] [value](#value) \[ [value](#value) ] `)`
<a name="pathpulsepercent_deltype"></a>pathpulsepercent\_deltype ::= `(` [PATHPULSEPERCENT](#PATHPULSEPERCENT) \[ [input_output_path](#input_output_path) ] [value](#value) \[ [value](#value) ] `)`
<a name="absolute_deltype"></a>absolute\_deltype ::= `(` [ABSOLUTE](#ABSOLUTE) [del_def](#del_def) \{ [del_def](#del_def) } `)`
<a name="increment_deltype"></a>increment\_deltype ::= `(` [INCREMENT](#INCREMENT) [del_def](#del_def) \{ [del_def](#del_def) } `)`
<a name="input_output_path"></a>input\_output\_path ::= [port_instance](#port_instance) [port_instance](#port_instance)
<a name="del_def"></a>del\_def ::= [iopath_def](#iopath_def) \| [cond_def](#cond_def) \| [condelse_def](#condelse_def) \| [port_del](#port_del) \| [interconnect_def](#interconnect_def) \| [netdelay_def](#netdelay_def) \| [device_def](#device_def)
<a name="iopath_def"></a>iopath\_def ::= `(` [IOPATH](#IOPATH) [port_spec](#port_spec) [port_instance](#port_instance) \{ [retain_def](#retain_def) } [delval_list](#delval_list) `)`
<a name="retain_def"></a>retain\_def ::= `(` [RETAIN](#RETAIN) [retval_list](#retval_list) `)`
<a name="cond_def"></a>cond\_def ::= `(` [COND](#COND) \[ [qstring](#qstring) ] [conditional_port_expr](#conditional_port_expr) [iopath_def](#iopath_def) `)`
<a name="condelse_def"></a>condelse\_def ::= `(` [CONDELSE](#CONDELSE) [iopath_def](#iopath_def) `)`
<a name="port_def"></a>port\_def ::= `(` [PORT](#PORT) [port_instance](#port_instance) [delval_list](#delval_list) `)`
<a name="interconnect_def"></a>interconnect\_def ::= `(` [INTERCONNECT](#INTERCONNECT) [port_instance](#port_instance) [port_instance](#port_instance) [delval_list](#delval_list) `)`
<a name="netdelay_def"></a>netdelay\_def ::= `(` [NETDELAY](#NETDELAY) [net_spec](#net_spec) [delval_list](#delval_list) `)`
<a name="device_def"></a>device\_def ::= `(` [DEVICE](#DEVICE) \[ [port_instance](#port_instance) ] [delval_list](#delval_list) `)`
<a name="tchk_def"></a>tchk\_def ::= [setup_timing_check](#setup_timing_check) \| [hold_timing_check](#hold_timing_check) \| [setuphold_timing_check](#setuphold_timing_check) \| [recovery_timing_check](#recovery_timing_check) \| [removal_timing_check](#removal_timing_check) \| [recrem_timing_check](#recrem_timing_check) \| [skew_timing_check](#skew_timing_check) \| [bidirectskew_timing_check](#bidirectskew_timing_check) \| [width_timing_check](#width_timing_check) \| [period_timing_check](#period_timing_check) \| [nochange_timing_check](#nochange_timing_check)
<a name="setup_timing_check"></a>setup\_timing\_check ::= `(` [SETUP](#SETUP) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [value](#value) `)`
<a name="hold_timing_check"></a>hold\_timing\_check ::= `(` [HOLD](#HOLD) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [value](#value) `)`
<a name="setuphold_timing_check"></a>setuphold\_timing\_check ::= `(` [SETUPHOLD](#SETUPHOLD) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [rvalue](#rvalue) [rvalue](#rvalue) `)` \| `(` [SETUPHOLD](#SETUPHOLD) [port_spec](#port_spec) [port_spec](#port_spec) [rvalue](#rvalue) [rvalue](#rvalue) \[ [scond](#scond) ] \[ [ccond](#ccond) ] `)`
<a name="recovery_timing_check"></a>recovery\_timing\_check ::= `(` [RECOVERY](#RECOVERY) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [value](#value) `)`
<a name="removal_timing_check"></a>removal\_timing\_check ::= `(` [REMOVAL](#REMOVAL) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [value](#value) `)`
<a name="recrem_timing_check"></a>recrem\_timing\_check ::= `(` [RECREM](#RECREM) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [rvalue](#rvalue) [rvalue](#rvalue) `)` \| `(` [RECREM](#RECREM) [port_spec](#port_spec) [port_spec](#port_spec) [rvalue](#rvalue) [rvalue](#rvalue) \[ [scond](#scond) ] \[ [ccond](#ccond) ] `)`
<a name="skew_timing_check"></a>skew\_timing\_check ::= `(` [SKEW](#SKEW) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [rvalue](#rvalue) `)`
<a name="bidirectskew_timing_check"></a>bidirectskew\_timing\_check ::= `(` [BIDIRECTSKEW](#BIDIRECTSKEW) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [value](#value) [value](#value) `)`
<a name="width_timing_check"></a>width\_timing\_check ::= `(` [WIDTH](#WIDTH) [port_tchk](#port_tchk) [value](#value) `)`
<a name="period_timing_check"></a>period\_timing\_check ::= `(` [PERIOD](#PERIOD) [port_tchk](#port_tchk) [value](#value) `)`
<a name="nochange_timing_check"></a>nochange\_timing\_check ::= `(` [NOCHANGE](#NOCHANGE) [port_tchk](#port_tchk) [port_tchk](#port_tchk) [rvalue](#rvalue) [rvalue](#rvalue) `)`
<a name="port_tchk"></a>port\_tchk ::= [port_spec](#port_spec) \| `(` [COND](#COND) \[ [qstring](#qstring) ] [timing_check_condition](#timing_check_condition) [port_spec](#port_spec) `)`
<a name="scond"></a>scond ::= `(` [SCOND](#SCOND) \[ [qstring](#qstring) ] [timing_check_condition](#timing_check_condition) `)`
<a name="ccond"></a>ccond ::= `(` [CCOND](#CCOND) \[ [qstring](#qstring) ] [timing_check_condition](#timing_check_condition) `)`
<a name="te_def"></a>te\_def ::= [cns_def](#cns_def) \| [tenv_def](#tenv_def)
<a name="cns_def"></a>cns\_def ::= [path_constraint](#path_constraint) \| [period_constraint](#period_constraint) \| [sum_constraint](#sum_constraint) \| [diff_constraint](#diff_constraint) \| [skew_constraint](#skew_constraint)
<a name="path_constraint"></a>path\_constraint ::= `(` [PATHCONSTRAINT](#PATHCONSTRAINT) \[ [name](#name) ] [port_instance](#port_instance) [port_instance](#port_instance) \{ [port_instance](#port_instance) } [rvalue](#rvalue) [rvalue](#rvalue) `)`
<a name="period_constraint"></a>period\_constraint ::=`(` [PERIODCONSTRAINT](#PERIODCONSTRAINT) [port_instance](#port_instance) [value](#value) \[ [exception](#exception) ] `)`
<a name="sum_constraint"></a>sum\_constraint ::= `(` [SUM](#SUM) [constraint_path](#constraint_path) [constraint_path](#constraint_path) \{ [constraint_path](#constraint_path) } [rvalue](#rvalue) \[ [rvalue](#rvalue) ] `)`
<a name="diff_constraint"></a>diff\_constraint ::= `(` [DIFF](#DIFF) [constraint_path](#constraint_path) [constraint_path](#constraint_path) [value](#value) \[ [value](#value) ] `)`
<a name="skew_constraint"></a>skew\_constraint ::= `(` [SKEWCONSTRAINT](#SKEWCONSTRAINT) [port_spec](#port_spec) [value](#value) `)`
<a name="exception"></a>exception ::= `(` [EXCEPTION](#EXCEPTION) [cell_instance](#cell_instance) \{ [cell_instance](#cell_instance) } `)`
<a name="name"></a>name ::= `(` [NAME](#NAME) \[ [qstring](#qstring) ] `)`
<a name="constraint_path"></a>constraint\_path ::= `(` [port_instance](#port_instance) [port_instance](#port_instance) `)`
<a name="tenv_def"></a>tenv\_def ::= [arrival_env](#arrival_env) \| [departure_env](#departure_env) \| [slack_env](#slack_env) \| [waveform_env](#waveform_env)
<a name="arrival_env"></a>arrival\_env ::= `(` [ARRIVAL](#ARRIVAL) \[ [port_edge](#port_edge) ] [port_instance](#port_instance) [rvalue](#rvalue) [rvalue](#rvalue) [rvalue](#rvalue) [rvalue](#rvalue) `)`
<a name="departure_env"></a>departure\_env ::= `(` [DEPARTURE](#DEPARTURE) \[ [port_edge](#port_edge) ] [port_instance](#port_instance) [rvalue](#rvalue) [rvalue](#rvalue) [rvalue](#rvalue) [rvalue](#rvalue) `)`
<a name="slack_env"></a>slack\_env ::= `(` [SLACK](#SLACK) [port_instance](#port_instance) [rvalue](#rvalue) [rvalue](#rvalue) [rvalue](#rvalue) [rvalue](#rvalue) \[ [real_number](#real_number) ] `)`
<a name="waveform_env"></a>waveform\_env ::= `(` [WAVEFORM](#WAVEFORM) [port_instance](#port_instance) [real_number](#real_number) [edge_list](#edge_list) `)`
<a name="edge_list"></a>edge\_list ::= [pos_pair](#pos_pair) \{ [pos_pair](#pos_pair) } \| [neg_pair](#neg_pair) \{ [neg_pair](#neg_pair) }
<a name="pos_pair"></a>pos\_pair ::= `(` [posedge](#posedge) [signed_real_number](#signed_real_number) \[ [signed_real_number](#signed_real_number) ] `)` `(` [negedge](#negedge) [signed_real_number](#signed_real_number) \[ [signed_real_number](#signed_real_number) ] `)`
<a name="neg_pair"></a>neg\_pair ::= `(` [negedge](#negedge) [signed_real_number](#signed_real_number) \[ [signed_real_number](#signed_real_number) ] `)` `(` [posedge](#posedge) [signed_real_number](#signed_real_number) \[ [signed_real_number](#signed_real_number) ] `)`
<a name="lbl_type"></a>lbl\_type ::= `(` [INCREMENT](#INCREMENT) [lbl_def](#lbl_def) \{ [lbl_def](#lbl_def) } `)` \| `(` [ABSOLUTE](#ABSOLUTE) [lbl_def](#lbl_def) \{ [lbl_def](#lbl_def) } `)`
<a name="lbl_def"></a>lbl\_def ::= `(` [identifier](#identifier) [delval_list](#delval_list) `)`
<a name="port_spec"></a>port\_spec ::= [port_instance](#port_instance) \| [port_edge](#port_edge)
<a name="port_edge"></a>port\_edge ::= `(` [edge_identifier](#edge_identifier) [port_instance](#port_instance) `)`
<a name="edge_identifier"></a>edge\_identifier ::= [posedge](#posedge) \| [negedge](#negedge) \| [01](#01) \| [10](#10) \| [0z](#0z) \| [z1](#z1) \| [1z](#1z) \| [z0](#z0)
<a name="port_instance"></a>port\_instance ::= [port](#port) \| [hierarchical_identifier](#hierarchical_identifier) [hchar](#hchar) [port](#port)
<a name="port"></a>port ::= [scalar_port](#scalar_port) \| [bus_port](#bus_port)
<a name="scalar_port"></a>scalar\_port ::= [hierarchical_identifier](#hierarchical_identifier) \| [hierarchical_identifier](#hierarchical_identifier) \[ [integer](#integer) ]
<a name="bus_port"></a>bus\_port ::= [hierarchical_identifier](#hierarchical_identifier) \[ [integer](#integer) `:` [integer](#integer) ]
<a name="net_spec"></a>net\_spec ::= [port_instance](#port_instance) \| [net_instance](#net_instance)
<a name="net_instance"></a>net\_instance ::= [net](#net) \| [hierarchical_identifier](#hierarchical_identifier) [hier_divider_char](#hier_divider_char) [net](#net)
<a name="net"></a>net ::= [scalar_net](#scalar_net) \| [bus_net](#bus_net)
<a name="scalar_net"></a>scalar\_net ::= [hierarchical_identifier](#hierarchical_identifier) \| [hierarchical_identifier](#hierarchical_identifier) \[ [integer](#integer) ]
<a name="bus_net"></a>bus\_net ::= [hierarchical_identifier](#hierarchical_identifier) \[ [integer](#integer) `:` [integer](#integer) ]
### A.1.4 Data values
<a name="value"></a>value ::= `(` \[ [real_number](#real_number) ] `)` \| `(` \[[triple](#triple)] `)`
<a name="triple"></a>triple ::= [real_number](#real_number) `:` \[ [real_number](#real_number) ] `:` \[ [real_number](#real_number) ] \| \[ [real_number](#real_number) ] `:` [real_number](#real_number) `:` \[ [real_number](#real_number) ] \| \[ [real_number](#real_number) ] `:` \[ [real_number](#real_number) ] `:` [real_number](#real_number)
<a name="rvalue"></a>rvalue ::= `(` \[ [signed_real_number](#signed_real_number) ] `)` \| `(` \[ [rtriple](#rtriple) ] `)`
<a name="rtriple"></a>rtriple ::= [signed_real_number](#signed_real_number) `:` \[ [signed_real_number](#signed_real_number) ] `:` \[ [signed_real_number](#signed_real_number) ] \| \[ [signed_real_number](#signed_real_number) ] `:` [signed_real_number](#signed_real_number) `:` \[ [signed_real_number](#signed_real_number) ] \| \[ [signed_real_number](#signed_real_number) ] `:` \[ [signed_real_number](#signed_real_number) ] `:` [signed_real_number](#signed_real_number)
<a name="delval"></a>delval ::= [rvalue](#rvalue) \| `(` [rvalue](#rvalue) [rvalue](#rvalue) `)` \| `(` [rvalue](#rvalue) [rvalue](#rvalue) [rvalue](#rvalue) `)`
<a name="delval_list"></a>delval\_list ::= [delval](#delval) \| [delval](#delval) [delval](#delval) \| [delval](#delval) [delval](#delval) [delval](#delval) \| [delval](#delval) [delval](#delval) [delval](#delval) [delval](#delval) \[ [delval](#delval) ] \[ [delval](#delval) ] \| [delval](#delval) [delval](#delval) [delval](#delval) [delval](#delval) [delval](#delval) [delval](#delval) [delval](#delval) \[ [delval](#delval) ] \[ [delval](#delval) ] \[ [delval](#delval) ] \[ [delval](#delval) ] \[ [delval](#delval) ]
<a name="retval_list"></a>retval\_list ::= [delval](#delval) \| [delval](#delval) [delval](#delval) \| [delval](#delval) [delval](#delval) [delval](#delval)
### A.1.5 Conditions for path delays
<a name="conditional_port_expr"></a>conditional\_port\_expr ::= [simple_expression](#simple_expression) \| `(` [conditional_port_expr](#conditional_port_expr) `)` \| [unary_operator](#unary_operator) `(` [conditional_port_expr](#conditional_port_expr) `)` \| [conditional_port_expr](#conditional_port_expr) [binary_operator](#binary_operator) [conditional_port_expr](#conditional_port_expr)
<a name="simple_expression"></a>simple\_expression ::= `(` [simple_expression](#simple_expression) `)` \| [unary_operator](#unary_operator) `(` [simple_expression](#simple_expression) `)` \| [port](#port) \| [unary_operator](#unary_operator) [port](#port) \| [scalar_constant](#scalar_constant) \| [unary_operator](#unary_operator) [scalar_constant](#scalar_constant) \| [simple_expression](#simple_expression) `?` [simple_expression](#simple_expression) `:` [simple_expression](#simple_expression) \| \{ [simple_expression](#simple_expression) \[ [concat_expression](#concat_expression) ] } \| \{ [simple_expression](#simple_expression) \{ [simple_expression](#simple_expression) \[ [concat_expression](#concat_expression) ] } }
<a name="concat_expression"></a>concat\_expression ::= `,` [simple_expression](#simple_expression)
### A.1.6 Conditions for timing checks
<a name="timing_check_condition"></a>timing\_check\_condition ::= [scalar_node](#scalar_node) \| [inversion_operator](#inversion_operator) [scalar_node](#scalar_node) \| [scalar_node](#scalar_node) [equality_operator](#equality_operator) [scalar_constant](#scalar_constant)
<a name="scalar_node"></a>scalar\_node ::= [scalar_port](#scalar_port) \| [scalar_net](#scalar_net)
<a name="scalar_net"></a>scalar\_net ::= [hierarchical_identifier](#hierarchical_identifier)
### A.1.7 Fundamental lexical elements
&nbsp;&nbsp;&nbsp;&nbsp;[White](#White) [space](#space) [is](#is) [normally](#normally) [permitted](#permitted) [between](#between) [lexical](#lexical) [tokens](#tokens)`,` [but](#but) [not](#not) [within](#within) [the](#the) [definitions](#definitions) [in](#in) [A](#A)`.`[1](#1)`.`[7](#7)`.`
<a name="identifier"></a>identifier ::= [character](#character) \{ [character](#character) }
<a name="hierarchical_identifier"></a>hierarchical\_identifier ::=[identifier](#identifier) \{ [hchar](#hchar) [identifier](#identifier) }
<a name="qstring"></a>qstring ::= `"` \{ [any_character](#any_character) } `"`
<a name="integer"></a>integer ::= [decimal_digit](#decimal_digit) \{ [decimal_digit](#decimal_digit) }
<a name="real_number"></a>real\_number ::= [integer](#integer) \| [integer](#integer) \[ `.` [integer](#integer) ] \| [integer](#integer) \[ `.` [integer](#integer) ] [e](#e) \[ [sign](#sign) ] [integer](#integer)
<a name="signed_real_number"></a>signed\_real\_number ::= \[ [sign](#sign) ] [real_number](#real_number)
<a name="sign"></a>sign ::= `+` \| `-`
<a name="hchar"></a>hchar ::= `.` \| `/`
<a name="character"></a>character ::= [alphanumeric](#alphanumeric) \| [escaped_character](#escaped_character)
<a name="escaped_character"></a>escaped\_character ::= `\` [character](#character) \| `\` [special_character](#special_character) \| `\"`
<a name="any_character"></a>any\_character ::= [character](#character) \| [special_character](#special_character) \| `\"`
<a name="decimal_digit"></a>decimal\_digit ::= [0](#0) \| [1](#1) \| [2](#2) \| [3](#3) \| [4](#4) \| [5](#5) \| [6](#6) \| [7](#7) \| [8](#8) \| [9](#9)
<a name="alphanumeric"></a>alphanumeric ::= [a](#a) \| [b](#b) \| [c](#c) \| [d](#d) \| [e](#e) \| [f](#f) \| [g](#g) \| [h](#h) \| [i](#i) \| [j](#j) \| [k](#k) \| [l](#l) \| [m](#m) \| [n](#n) \| [o](#o) \| [p](#p) \| [q](#q) \| [r](#r) \| [s](#s) \| [t](#t) \| [u](#u) \| [v](#v) \| [w](#w) \| [x](#x) \| [y](#y) \| [z](#z) \| [A](#A) \| [B](#B) \| [C](#C) \| [D](#D) \| [E](#E) \| [F](#F) \| [G](#G) \| [H](#H) \| [I](#I) \| [J](#J) \| [K](#K) \| [L](#L) \| [M](#M) \| [N](#N) \| [O](#O) \| [P](#P) \| [Q](#Q) \| [R](#R) \| [S](#S) \| [T](#T) \| [U](#U) \| [V](#V) \| [W](#W) \| [X](#X) \| [Y](#Y) \| [Z](#Z) \| [_](#_) \| `$` \| [decimal_digit](#decimal_digit)
<a name="special_character"></a>special\_character ::= `!` \| `#` \| `%` \| `&` \| `«` \| `(` \| `)` \| `*` \| `+` \| `,` \| `-` \| `.` \| `/` \| `:` \| `;` \| `<` \| `=` \| `>` \| `?` \| `@` \| \[ \| `\` \| ] \| `^` \| `‘` \| \{ \| \| \| } \| `~`
### A.1.8 Constants for expressions
<a name="scalar_constant"></a>scalar\_constant ::= [0](#0) \| [b0](#b0) \| [B0](#B0) \| [1](#1) [b0](#b0) \| [1](#1) [B0](#B0) \| [1](#1) \| [b1](#b1) \| [B1](#B1) \| [1](#1) [b1](#b1) \| [1](#1) [B1](#B1)
### A.1.9 Operators for expressions
<a name="unary_operator"></a>unary\_operator ::= `+` \| `-` \| `!` \| `~` \| `&` \| `~&` \| \| \| `~|` \| `^` \| `^~` \| `~^`
<a name="inversion_operator"></a>inversion\_operator ::= `!` \| `~`
<a name="binary_operator"></a>binary\_operator ::= `+` \| `-` \| `*` \| `/` \| `%` \| `==` \| `!=` \| `===` \| `!==` \| `&&` \| `||` \| `<` \| `<=` \| `>` \| `>=` \| `&` \| \| \| `^` \| `^~` \| `~^` \| `>>` \| `<<`
<a name="equality_operator"></a>equality\_operator ::= `==` \| `!=` \| `===` \| `!==`
### A.1.10 Precedence rules of SDF operators
&nbsp;&nbsp;&nbsp;&nbsp;`!` `~` [highest](#highest) [precedence](#precedence)
&nbsp;&nbsp;&nbsp;&nbsp;`*` `/` `%`
&nbsp;&nbsp;&nbsp;&nbsp;`+` `-`
&nbsp;&nbsp;&nbsp;&nbsp;`<<` `>>`
&nbsp;&nbsp;&nbsp;&nbsp;`<` `<=` `>` `>=`
&nbsp;&nbsp;&nbsp;&nbsp;`==` `!=` `===` `!==`
&nbsp;&nbsp;&nbsp;&nbsp;`&`
&nbsp;&nbsp;&nbsp;&nbsp;`^` `^~`
&nbsp;&nbsp;&nbsp;&nbsp;\|
&nbsp;&nbsp;&nbsp;&nbsp;`&&`
&nbsp;&nbsp;&nbsp;&nbsp;`||` [lowest](#lowest) [precedence](#precedence)
