%---------------------------------------------------------------------------%
% json2dir: create the directory tree a JSON document describes, in the
% current directory. Implements RFC J2D-1
% (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
%
% Mercury standard library only: a hand-written strict UTF-8 check and JSON
% parser over the bytes of stdin, plus a few foreign_proc("C", ...) calls for
% the POSIX operations the standard library does not offer.
%---------------------------------------------------------------------------%

:- module json2dir.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is cc_multi.

%---------------------------------------------------------------------------%

:- implementation.

:- import_module bitmap.
:- import_module exception.
:- import_module int.
:- import_module list.
:- import_module map.
:- import_module pair.
:- import_module string.
:- import_module univ.

:- type j2d_error
    --->    j2d_error(string).

    % Strings and names are kept as lists of UTF-8 bytes, because file
    % contents may contain NUL, which a Mercury string cannot hold.
:- type bytes == list(int).

:- type json
    --->    jstr(bytes)
    ;       jarr(list(json))
    ;       jobj(list(pair(bytes, json)))
    ;       jlit(string).           % a number, true, false or null

:- pred err(string::in) is erroneous.

err(Msg) :-
    throw(j2d_error(Msg)).

%---------------------------------------------------------------------------%
% Main.

main(!IO) :-
    io.command_line_arguments(Args, !IO),
    (
        Args = [],
        try_io(run, Result, !IO),
        (
            Result = succeeded(_)
        ;
            Result = exception(Univ),
            ( if univ_to_type(Univ, j2d_error(Msg)) then
                Text = Msg
            else
                Text = string.string(univ_value(Univ))
            ),
            io.stderr_stream(Stderr, !IO),
            io.write_string(Stderr, "json2dir: " ++ Text ++ "\n", !IO),
            io.set_exit_status(1, !IO)
        )
    ;
        Args = [_ | _],
        io.stderr_stream(Stderr, !IO),
        io.write_string(Stderr, "usage: json2dir < document.json\n", !IO),
        io.set_exit_status(2, !IO)
    ).

:- pred run(int::out, io::di, io::uo) is det.

run(0, !IO) :-
    io.binary_input_stream(Stdin, !IO),
    io.read_binary_file(Stdin, ReadResult, !IO),
    (
        ReadResult = ok(Bytes0)
    ;
        ReadResult = eof,
        Bytes0 = []
    ;
        ReadResult = error(E),
        err("cannot read standard input: " ++ io.error_message(E))
    ),
    % §3: a byte order mark at the start may be ignored.
    ( if Bytes0 = [0xEF, 0xBB, 0xBF | Rest] then Bytes = Rest else Bytes = Bytes0 ),
    check_utf8(Bytes),
    parse_value(Doc, Bytes, After0),
    skip_ws(After0, After),
    (
        After = []
    ;
        After = [_ | _],
        err("input is not valid JSON: trailing data after the value")
    ),
    (
        Doc = jobj(Members),
        validate(".", Doc),
        apply(".", Members, !IO)
    ;
        ( Doc = jstr(_)
        ; Doc = jarr(_)
        ; Doc = jlit(_)
        ),
        err("the root of the document must be an object")
    ).

%---------------------------------------------------------------------------%
% Strict UTF-8 (RFC 3629): no overlong forms, no surrogates, max U+10FFFF.

:- pred check_utf8(bytes::in) is det.

check_utf8([]).
check_utf8([B | Bs]) :-
    ( if B < 0x80 then
        check_utf8(Bs)
    else if B >= 0xC2, B =< 0xDF then
        cont(0x80, 0xBF, Bs, R), check_utf8(R)
    else if B = 0xE0 then
        cont(0xA0, 0xBF, Bs, R1), cont(0x80, 0xBF, R1, R), check_utf8(R)
    else if B = 0xED then
        cont(0x80, 0x9F, Bs, R1), cont(0x80, 0xBF, R1, R), check_utf8(R)
    else if B >= 0xE1, B =< 0xEF then
        cont(0x80, 0xBF, Bs, R1), cont(0x80, 0xBF, R1, R), check_utf8(R)
    else if B = 0xF0 then
        cont(0x90, 0xBF, Bs, R1), cont(0x80, 0xBF, R1, R2),
        cont(0x80, 0xBF, R2, R), check_utf8(R)
    else if B >= 0xF1, B =< 0xF3 then
        cont(0x80, 0xBF, Bs, R1), cont(0x80, 0xBF, R1, R2),
        cont(0x80, 0xBF, R2, R), check_utf8(R)
    else if B = 0xF4 then
        cont(0x80, 0x8F, Bs, R1), cont(0x80, 0xBF, R1, R2),
        cont(0x80, 0xBF, R2, R), check_utf8(R)
    else
        err("input is not valid UTF-8")
    ).

:- pred cont(int::in, int::in, bytes::in, bytes::out) is det.

cont(Lo, Hi, Bs, Rest) :-
    ( if Bs = [C | Rest0], C >= Lo, C =< Hi then
        Rest = Rest0
    else
        err("input is not valid UTF-8")
    ).

%---------------------------------------------------------------------------%
% Strict JSON (RFC 8259) parser over bytes.

:- pred syntax(string::in) is erroneous.

syntax(Msg) :-
    err("input is not valid JSON: " ++ Msg).

:- pred skip_ws(bytes::in, bytes::out) is det.

skip_ws(In, Out) :-
    ( if In = [C | Rest], ( C = 0x20 ; C = 0x09 ; C = 0x0A ; C = 0x0D ) then
        skip_ws(Rest, Out)
    else
        Out = In
    ).

:- pred parse_value(json::out, bytes::in, bytes::out) is det.

parse_value(V, !S) :-
    skip_ws(!S),
    (
        !.S = [],
        syntax("unexpected end of input")
    ;
        !.S = [C | R],
        ( if C = 123 then         % {
            parse_object(V, R, !:S)
        else if C = 91 then       % [
            parse_array(V, R, !:S)
        else if C = 34 then       % "
            parse_string(Str, R, !:S),
            V = jstr(Str)
        else if C = 0't then
            literal([0't, 0'r, 0'u, 0'e], !S),
            V = jlit("true")
        else if C = 0'f then
            literal([0'f, 0'a, 0'l, 0's, 0'e], !S),
            V = jlit("false")
        else if C = 0'n then
            literal([0'n, 0'u, 0'l, 0'l], !S),
            V = jlit("null")
        else if ( C = 45 ; is_digit(C) ) then
            parse_number(!S),
            V = jlit("number")
        else
            syntax("unexpected character")
        )
    ).

:- pred is_digit(int::in) is semidet.

is_digit(C) :-
    C >= 0'0, C =< 0'9.

:- pred literal(bytes::in, bytes::in, bytes::out) is det.

literal([], !S).
literal([L | Ls], !S) :-
    ( if !.S = [L | R] then
        literal(Ls, R, !:S)
    else
        syntax("invalid literal")
    ).

:- pred parse_object(json::out, bytes::in, bytes::out) is det.

parse_object(V, !S) :-
    skip_ws(!S),
    ( if !.S = [125 | R] then
        !:S = R,
        V = jobj([])
    else
        parse_members([], Ms, !S),
        V = jobj(Ms)
    ).

:- pred parse_members(list(pair(bytes, json))::in,
    list(pair(bytes, json))::out, bytes::in, bytes::out) is det.

parse_members(Acc, Ms, !S) :-
    skip_ws(!S),
    ( if !.S = [34 | R] then
        parse_string(Key, R, !:S)
    else
        syntax("expected a member name")
    ),
    skip_ws(!S),
    ( if !.S = [58 | R2] then
        !:S = R2
    else
        syntax("expected ':'")
    ),
    parse_value(Val, !S),
    skip_ws(!S),
    Acc1 = [Key - Val | Acc],
    ( if !.S = [44 | R3] then
        parse_members(Acc1, Ms, R3, !:S)
    else if !.S = [125 | R4] then
        !:S = R4,
        Ms = list.reverse(Acc1)
    else
        syntax("expected ',' or '}'")
    ).

:- pred parse_array(json::out, bytes::in, bytes::out) is det.

parse_array(V, !S) :-
    skip_ws(!S),
    ( if !.S = [93 | R] then
        !:S = R,
        V = jarr([])
    else
        parse_elements([], Es, !S),
        V = jarr(Es)
    ).

:- pred parse_elements(list(json)::in, list(json)::out,
    bytes::in, bytes::out) is det.

parse_elements(Acc, Es, !S) :-
    parse_value(Val, !S),
    skip_ws(!S),
    Acc1 = [Val | Acc],
    ( if !.S = [44 | R] then
        parse_elements(Acc1, Es, R, !:S)
    else if !.S = [93 | R2] then
        !:S = R2,
        Es = list.reverse(Acc1)
    else
        syntax("expected ',' or ']'")
    ).

    % Called after the opening quote; returns the decoded UTF-8 bytes.
:- pred parse_string(bytes::out, bytes::in, bytes::out) is det.

parse_string(Str, !S) :-
    string_chars([], Rev, !S),
    Str = list.reverse(Rev).

:- pred string_chars(bytes::in, bytes::out, bytes::in, bytes::out) is det.

string_chars(Acc, Out, !S) :-
    (
        !.S = [],
        syntax("unterminated string")
    ;
        !.S = [C | R],
        ( if C = 34 then
            !:S = R,
            Out = Acc
        else if C = 92 then
            parse_escape(Acc, Acc1, R, !:S),
            string_chars(Acc1, Out, !S)
        else if C < 0x20 then
            syntax("control character in string")
        else
            string_chars([C | Acc], Out, R, !:S)
        )
    ).

:- pred parse_escape(bytes::in, bytes::out, bytes::in, bytes::out) is det.

parse_escape(Acc, Acc1, !S) :-
    (
        !.S = [],
        syntax("unterminated string")
    ;
        !.S = [E | R],
        !:S = R,
        ( if E = 34 then Acc1 = [34 | Acc]
        else if E = 92 then Acc1 = [92 | Acc]
        else if E = 0'/ then Acc1 = [0'/ | Acc]
        else if E = 0'b then Acc1 = [8 | Acc]
        else if E = 0'f then Acc1 = [12 | Acc]
        else if E = 0'n then Acc1 = [10 | Acc]
        else if E = 0'r then Acc1 = [13 | Acc]
        else if E = 0't then Acc1 = [9 | Acc]
        else if E = 0'u then
            hex4(U, !S),
            ( if U >= 0xD800, U =< 0xDBFF then
                ( if !.S = [92, 0'u | R2] then
                    hex4(L, R2, !:S),
                    ( if L >= 0xDC00, L =< 0xDFFF then
                        Cp = 0x10000 + ((U - 0xD800) << 10) + (L - 0xDC00)
                    else
                        err("string contains an unpaired surrogate")
                    )
                else
                    err("string contains an unpaired surrogate")
                )
            else if U >= 0xDC00, U =< 0xDFFF then
                err("string contains an unpaired surrogate")
            else
                Cp = U
            ),
            Acc1 = list.reverse(encode_utf8(Cp)) ++ Acc
        else
            syntax("invalid escape")
        )
    ).

:- pred hex4(int::out, bytes::in, bytes::out) is det.

hex4(V, !S) :-
    ( if
        !.S = [A, B, C, D | R],
        hex(A, HA), hex(B, HB), hex(C, HC), hex(D, HD)
    then
        V = (((HA * 16 + HB) * 16 + HC) * 16 + HD),
        !:S = R
    else
        syntax("invalid \\u escape")
    ).

:- pred hex(int::in, int::out) is semidet.

hex(C, V) :-
    ( if C >= 0'0, C =< 0'9 then V = C - 0'0
    else if C >= 0'a, C =< 0'f then V = C - 0'a + 10
    else C >= 0'A, C =< 0'F, V = C - 0'A + 10
    ).

:- func encode_utf8(int) = bytes.

encode_utf8(Cp) = Bytes :-
    ( if Cp < 0x80 then
        Bytes = [Cp]
    else if Cp < 0x800 then
        Bytes = [0xC0 \/ (Cp >> 6), 0x80 \/ (Cp /\ 0x3F)]
    else if Cp < 0x10000 then
        Bytes = [0xE0 \/ (Cp >> 12), 0x80 \/ ((Cp >> 6) /\ 0x3F),
            0x80 \/ (Cp /\ 0x3F)]
    else
        Bytes = [0xF0 \/ (Cp >> 18), 0x80 \/ ((Cp >> 12) /\ 0x3F),
            0x80 \/ ((Cp >> 6) /\ 0x3F), 0x80 \/ (Cp /\ 0x3F)]
    ).

:- pred parse_number(bytes::in, bytes::out) is det.

parse_number(!S) :-
    ( if !.S = [45 | R] then !:S = R else true ),
    ( if !.S = [0'0 | R1] then
        !:S = R1
    else if !.S = [C | _], is_digit(C) then
        digits(!S)
    else
        syntax("invalid number")
    ),
    ( if !.S = [46 | R2] then
        ( if R2 = [C2 | _], is_digit(C2) then digits(R2, !:S)
        else syntax("invalid number") )
    else
        true
    ),
    ( if !.S = [E | R3], ( E = 0'e ; E = 0'E ) then
        ( if R3 = [Sg | R4], ( Sg = 43 ; Sg = 45 ) then R5 = R4 else R5 = R3 ),
        ( if R5 = [C3 | _], is_digit(C3) then digits(R5, !:S)
        else syntax("invalid number") )
    else
        true
    ).

:- pred digits(bytes::in, bytes::out) is det.

digits(In, Out) :-
    ( if In = [C | R], is_digit(C) then digits(R, Out) else Out = In ).

%---------------------------------------------------------------------------%
% Validation of the whole document (§4) before touching the file system.

:- func show(bytes) = string.

show(Bs) = ( if string.from_code_unit_list(Bs, S) then S else "<name>" ).

:- func child(string, bytes) = string.

child(Where, Name) =
    ( if Where = "." then show(Name) else Where ++ "/" ++ show(Name) ).

:- pred validate(string::in, json::in) is det.

validate(_, jstr(_)).
validate(Where, jlit(L)) :-
    err(Where ++ ": " ++ L ++ " values are not allowed").
validate(Where, jarr(Es)) :-
    ( if Es = [jstr(Kind), jstr(Payload)] then
        ( if Kind = link_kind then
            ( if list.member(0, Payload) then
                err(Where ++ ": a link target cannot contain NUL")
            else
                true
            )
        else if Kind = script_kind then
            true
        else
            err(Where ++ ": unknown array kind")
        )
    else
        err(Where ++
            ": an array must be [\"link\", target] or [\"script\", content]")
    ).
validate(Where, jobj(Ms)) :-
    list.foldl(validate_member(Where), Ms, 0, _).

:- pred validate_member(string::in, pair(bytes, json)::in,
    int::in, int::out) is det.

validate_member(Where, Name - Value, !N) :-
    Child = child(Where, Name),
    ( if
        ( Name = []
        ; Name = [0'.]
        ; Name = [0'., 0'.]
        ; list.member(0'/, Name)
        ; list.member(0, Name)
        )
    then
        err(Child ++ ": invalid name")
    else
        true
    ),
    validate(Child, Value),
    !:N = !.N + 1.

:- func link_kind = bytes.
link_kind = [0'l, 0'i, 0'n, 0'k].

:- func script_kind = bytes.
script_kind = [0's, 0'c, 0'r, 0'i, 0'p, 0't].

%---------------------------------------------------------------------------%
% Creating the tree (§5).

:- pred apply(string::in, list(pair(bytes, json))::in, io::di, io::uo) is det.

apply(Dir, Members, !IO) :-
    % Duplicate names: the last occurrence wins. map orders the names by
    % their UTF-8 bytes, like the reference implementation.
    Map = list.foldl((func(K - V, M0) = map.set(M0, K, V)), Members, map.init),
    map.foldl(apply_member(Dir), Map, !IO).

:- pred apply_member(string::in, bytes::in, json::in, io::di, io::uo) is det.

apply_member(Dir, NameBytes, Value, !IO) :-
    ( if string.from_code_unit_list(NameBytes, Name0) then
        Name = Name0
    else
        err("invalid name")
    ),
    Path = Dir ++ "/" ++ Name,
    lstat_kind(Path, Kind, !IO),
    ( if Kind < 0 then
        err(Path ++ ": cannot inspect existing entry")
    else
        true
    ),
    (
        Value = jstr(Content),
        clear(Path, Kind, !IO),
        write_file(Path, Content, 0, !IO)
    ;
        Value = jarr(Es),
        clear(Path, Kind, !IO),
        ( if Es = [jstr(K), jstr(Payload)] then
            ( if K = link_kind then
                ( if string.from_code_unit_list(Payload, Target) then
                    io.make_symlink(Target, Path, Res, !IO),
                    check(Path, Res)
                else
                    err(Path ++ ": invalid link target")
                )
            else
                write_file(Path, Payload, 1, !IO)
            )
        else
            err(Path ++ ": invalid array")
        )
    ;
        Value = jobj(Ms),
        ( if Kind = 1 then
            true
        else
            ( if Kind = 2 then
                io.remove_file(Path, RRes, !IO),
                check(Path, RRes)
            else
                true
            ),
            dir.make_single_directory(Path, MRes, !IO),
            check(Path, MRes)
        ),
        apply(Path, Ms, !IO)
    ;
        Value = jlit(_),
        err(Path ++ ": invalid value")
    ).

    % §5.2-5.4: remove an existing non-directory; a directory is in the way.
:- pred clear(string::in, int::in, io::di, io::uo) is det.

clear(Path, Kind, !IO) :-
    ( if Kind = 1 then
        err(Path ++ ": a directory is in the way")
    else if Kind = 2 then
        io.remove_file(Path, Res, !IO),
        check(Path, Res)
    else
        true
    ).

:- pred check(string::in, io.res::in) is det.

check(_, ok).
check(Path, error(E)) :-
    err(Path ++ ": " ++ io.error_message(E)).

:- pred write_file(string::in, bytes::in, int::in, io::di, io::uo) is det.

write_file(Path, Content, Exec, !IO) :-
    Bitmap = to_bitmap(Content),
    write_bitmap_file(Path, Bitmap, Exec, Error, !IO),
    ( if Error = "" then true else err(Path ++ ": " ++ Error) ).

:- func to_bitmap(bytes) = bitmap.
:- mode to_bitmap(in) = bitmap_uo is det.

to_bitmap(Bytes) = BM :-
    BM0 = bitmap.init(list.length(Bytes) * bits_per_byte),
    fill(Bytes, 0, BM0, BM).

:- pred fill(bytes::in, int::in, bitmap::bitmap_di, bitmap::bitmap_uo) is det.

fill([], _, !BM).
fill([B | Bs], I, !BM) :-
    !BM ^ byte(I) := B,
    fill(Bs, I + 1, !BM).

%---------------------------------------------------------------------------%
% POSIX operations the standard library lacks.

:- import_module dir.

:- pragma foreign_decl("C", "
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
").

    % 0 = no entry, 1 = directory, 2 = anything else (never followed),
    % -1 = error.
:- pred lstat_kind(string::in, int::out, io::di, io::uo) is det.

:- pragma foreign_proc("C",
    lstat_kind(Path::in, Kind::out, _IO0::di, _IO::uo),
    [will_not_call_mercury, promise_pure, thread_safe],
"
    struct stat st;
    if (lstat(Path, &st) != 0) {
        Kind = (errno == ENOENT) ? 0 : -1;
    } else {
        Kind = S_ISDIR(st.st_mode) ? 1 : 2;
    }
").

    % Create a new file (O_EXCL, never through a link) with the bytes of
    % the bitmap; with Exec = 1, add the execute bits 0111.
    % Error is \"\" on success, otherwise a description.
:- pred write_bitmap_file(string::in, bitmap::bitmap_ui, int::in,
    string::out, io::di, io::uo) is det.

:- pragma foreign_proc("C",
    write_bitmap_file(Path::in, Bitmap::bitmap_ui, Exec::in, Error::out,
        _IO0::di, _IO::uo),
    [will_not_call_mercury, promise_pure, thread_safe],
"
    const char *msg = NULL;
    int fd = open(Path, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0666);
    if (fd < 0) {
        msg = strerror(errno);
    } else {
        const unsigned char *p = (const unsigned char *) Bitmap->elements;
        size_t n = (size_t) (Bitmap->num_bits / 8);
        while (n > 0 && msg == NULL) {
            ssize_t w = write(fd, p, n);
            if (w < 0) {
                if (errno != EINTR) msg = strerror(errno);
            } else {
                p += w;
                n -= (size_t) w;
            }
        }
        if (msg == NULL && Exec) {
            struct stat st;
            if (fstat(fd, &st) != 0 ||
                fchmod(fd, (st.st_mode & 07777) | 0111) != 0)
            {
                msg = strerror(errno);
            }
        }
        if (close(fd) != 0 && msg == NULL) msg = strerror(errno);
    }
    if (msg == NULL) msg = \"\";
    MR_make_aligned_string_copy(Error, msg);
").

%---------------------------------------------------------------------------%
:- end_module json2dir.
%---------------------------------------------------------------------------%
