
$(
###############################################################################
  FIRST-ORDER LOGIC WITH EQUALITY
###############################################################################

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This section includes a few "housekeeping" mechanisms before we begin
  defining the basics of logic.

$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $.  $( Right arrow (read:  "implies") $)
  $c -. $.  $( Right handle (read:  "not") $)
  $c wff $.  $( Well-formed formula symbol (read:  "the following symbol
                sequence is a wff") $)
  $c |- $.  $( Turnstile (read:  "the following symbol sequence is provable" or
               "a proof exists for") $)

  $( Define the syntax and logical typecodes, and declare that our grammar is
     unambiguous (verifiable using the KLR parser, with compositing depth 5).
     (This $ j comment need not be read by verifiers, but is useful for parsers
     like mmj2.) $)
  $( $j
    syntax 'wff';
    syntax '|-' as 'wff';
    unambiguous 'klr 5';
  $)

  $( Declare the color of wff variables. $)
  $( $j
    varcolorcode "wff" as "0000FF";
    altvarcolorcode "wff" as "337DFF";
  $)

  $( Declare typographical constant symbols that are not directly used in the
     formalism but are useful to explain it in comments. $)

  $c & $.  $( Ampersand (read: "and"). $)
  $c => $.  $( Double right arrow (read: "implies"). $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Inferences for assisting proof development
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The inference rules in this section will normally never appear in a completed
  proof.  They can be ignored if you are using this database to assist learning
  logic - please start with the statement ~ wn instead.

$)

  ${
    idi.1 $e |- ph $.
    $( (_Note_:  This inference rule and the next one, ~ a1ii , will normally
       never appear in a completed proof.  They can be ignored if you are using
       this database to assist learning logic; please start with the statement
       ~ wn instead.)

       This inference says "if ` ph ` is true then ` ph ` is true".  This
       inference requires no axioms for its proof, and is useful as a
       copy-paste mechanism during proof development in mmj2.  It is normally
       not referenced in the final version of a proof, since it is always
       redundant.  You can remove this using the metamath-exe (Metamath
       program) Proof Assistant using the "MM-PA> MINIMIZE__WITH *" command.
       This is the inference associated with ~ id , hence its name.
       (Contributed by Alan Sare, 31-Dec-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idi $p |- ph $=
      (  ) B $.
  $}

  ${
    a1ii.1 $e |- ph $.
    a1ii.2 $e |- ps $.
    $( (_Note_:  This inference rule and the previous one, ~ idi , will
       normally never appear in a completed proof.)

       This is a technical inference to assist proof development.  It provides
       a temporary way to add an independent subproof to a proof under
       development, for later assignment to a normal proof step.

       The Metamath (Metamath-exe) program Proof Assistant requires proofs to
       be developed backwards from the conclusion with no gaps, and it has no
       mechanism that lets the user work on isolated subproofs.  This inference
       provides a workaround for this limitation.  It can be inserted at any
       point in a proof to allow an independent subproof to be developed on the
       side, for later use as part of the final proof.

       _Instructions_:
       <HTML><ol><li>Assign this inference to any unknown step in the proof.
       Typically, the last unknown step is the most convenient, since
       <code>MM-PA&gt; ASSIGN LAST</code> can be used.  This step will be
       replicated in hypothesis a1ii.1, from where the development of the main
       proof can continue.</li><li>Develop the independent subproof backwards
       from hypothesis a1ii.2.  If desired, use a
       <code>MM-PA&gt; LET STEP</code>
       command to pre-assign the conclusion of the independent subproof to
       a1ii.2.</li><li>After the independent subproof is complete, use
       <code>MM-PA&gt; IMPROVE ALL</code>
       to assign it automatically to an unknown
       step in the main proof that matches it.</li><li>After the entire proof
       is complete, use <code>MM-PA> MINIMIZE_WITH *</code> to clean up
       (discard) all ~ a1ii references automatically.</ol></HTML>

       This can also be used to apply subproofs from other theorems.  In step
       2, simply assign the theorem to a1ii.2, and run
       <HTML><code>MM-PA&gt; EXPAND &lt;theorem&gt;</code></HTML>
       to "import" a subproof
       from another theorem.

       This inference was originally designed to assist importing partially
       completed Proof Worksheets from the mmj2 Proof Assistant GUI, but it can
       also be useful on its own.  Interestingly, no axioms are required for
       its proof.  It is the inference associated with ~ a1i .  (Contributed by
       NM, 7-Feb-2006.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    a1ii $p |- ph $=
      (  ) C $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Propositional calculus deals with general truths about well-formed formulas
  (wffs) regardless of how they are constructed.  The simplest propositional
  truth is ` ( ph -> ph ) ` , which can be read "if something is true, then it
  is true" - rather trivial and obvious, but nonetheless it must be proved from
  the axioms (see Theorem ~ id ).

  The propositional calculus used here is a many valued system, using Jan
  Lukasiewicz's three valued logic. It contains different axioms. {TODO}

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ". $)
  wn $a wff -. ph $.

  $( Register negation '-.' as a primitive expression (lacking a definition).
    $)
  $( $j primitive 'wn'; $)

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ". $)
  wi $a wff ( ph -> ps ) $.

  $( Register implication '->' as a primitive expression (lacking a
    definition). $)
  $( $j primitive 'wi'; $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The axioms of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Avron, Arnon. (2000). Natural 3-valued Logics - Characterization and Proof
  Theory. Journal of Symbolic Logic. 56. 10.2307/2274919.
$)


  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  (Contributed by NM, 30-Sep-1992.) $)
    ax-mp $a |- ps $.
  $}

  $( Axiom I1.  (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
  ax-i1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( Axiom I2.  (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
  ax-i2 $a |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $.

  $( Axiom I3.  (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
  ax-i3 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $.

  $( Axiom I4.  (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
  ax-i4 $a |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $.

  $( Axiom I5.  (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
  ax-i5 $a |- ( ( ( ( ( ph -> ps ) -> ph ) -> ph ) -> ( ps -> ch ) )
  -> ( ps -> ch ) ) $.

  $( Axiom N1.  (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
  ax-n1 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

$)

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.) $)
    mp2 $p |- ch $=
      ( wi ax-mp ) BCEABCGDFHH $.
  $}

  ${
    mp2b.1 $e |- ph $.
    mp2b.2 $e |- ( ph -> ps ) $.
    mp2b.3 $e |- ( ps -> ch ) $.
    $( A double modus ponens inference.  (Contributed by Mario Carneiro,
       24-Jan-2013.) $)
    mp2b $p |- ch $=
      ( ax-mp ) BCABDEGFG $.
  $}

  ${
    a1i.1 $e |- ph $.
    $( Inference introducing an antecedent.  (Contributed by Lllllllllwith10ls,
       25-May-2026.) $)
    a1i $p |- ( ps -> ph ) $=
      ( wi ax-i1 ax-mp ) ABADCABEF $.
  $}

  ${
    2a1i.1 $e |- ph $.
    $( Inference introducing two antecedents.  (Contributed by
       Lllllllllwith10ls, 25-May-2026.) $)
    2a1i $p |- ( ps -> ( ch -> ph ) ) $=
      ( wi a1i ) CAEBACDFF $.
  $}
  
    $( Weaken ~ ax-i1 . (Contributed by film2860, 22-Jul-2026.) $)
    axl1w $p |- ( ph -> ( ps -> ( ch -> ps ) ) ) $=
      ( wi ax-i1 a1i ) BCBDDABCEF $.

  ${
    mp1i.1 $e |- ph $.
    mp1i.2 $e |- ( ph -> ps ) $.
    $( Inference detaching an antecedent and introducing a new one.
       (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
    mp1i $p |- ( ch -> ps ) $=
      ( ax-mp a1i ) BCABDEFG $.
  $}

  ${
    $( First of 2 premises for ~ syl . $)
    syl.1 $e |- ( ph -> ps ) $.
    $( Second of 2 premises for ~ syl . $)
    syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication (Contributed
       by Lllllllllwith10ls, 25-May-2026.) $)
    syl $p |- ( ph -> ch ) $=
      ( wi ax-i2 mp2 ) ABFBCFACFDEABCGH $.
  $}


  ${
    3syl.1 $e |- ( ph -> ps ) $.
    3syl.2 $e |- ( ps -> ch ) $.
    3syl.3 $e |- ( ch -> th ) $.
    $( Inference chaining two syllogisms ~ syl .  Inference associated with
       ~ imim12i .  (Contributed by NM, 28-Dec-1992.) $)
    3syl $p |- ( ph -> th ) $=
      ( syl ) ACDABCEFHGH $.
  $}

  ${
    4syl.1 $e |- ( ph -> ps ) $.
    4syl.2 $e |- ( ps -> ch ) $.
    4syl.3 $e |- ( ch -> th ) $.
    4syl.4 $e |- ( th -> ta ) $.
    $( Inference chaining three syllogisms ~ syl .  (Contributed by BJ,
       14-Jul-2018.)  The use of this theorem is marked "discouraged" because
       it can cause the Metamath program "MM-PA> MINIMIZE__WITH *" command to
       have very long run times.  However, feel free to use "MM-PA>
       MINIMIZE__WITH 4syl / OVERRIDE" if you wish.  Remember to update the
       "discouraged" file if it gets used.  (New usage is discouraged.) $)
    4syl $p |- ( ph -> ta ) $=
      ( 3syl syl ) ADEABCDFGHJIK $.
  $}

  ${
    mpi.1 $e |- ps $.
    mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested modus ponens inference.  (Contributed by Lllllllllwith10ls,
       25-May-2026.) $)
    mpi $p |- ( ph -> ch ) $=
      ( wi ax-i3 mp2 ) ABCFFBACFEDABCGH $.
  $}
  
  ${
    mpiALT.1 $e |- ps $.
    mpiALT.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( ~ mpi but with ~ ax-i4 instead of ~ ax-i3 . (Contributed by film2860, 22-Jul-2026.) $)
    mpiALT $p |- ( ph -> ch ) $=
      ( wi a1i ax-i4 ax-i2 ax-mp syl ) CBFBFACFBCBFDGCBFBFBCFCFACFCBHABCFFBCFCF
      ACFFEABCFCIJKJ $.
  $}

  ${
    mpisyl.1 $e |- ( ph -> ps ) $.
    mpisyl.2 $e |- ch $.
    mpisyl.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism combined with a modus ponens inference.  (Contributed by
       Alan Sare, 25-Jul-2011.) $)
    mpisyl $p |- ( ph -> th ) $=
      ( mpi syl ) ABDEBCDFGHI $.
  $}

  ${
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication.  Its
       associated inference is ~ mpi .  (Contributed by NM, 29-Dec-1992.)
       (Proof shortened by Wolf Lammen, 4-Aug-2012.) $)
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      ( wi ax-i3 ax-mp ) ABCEEBACEEDABCFG $.
  $}

  ${
    com12ALT.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( ~ com12 but with ~ ax-i4 instead of ~ ax-i3 . (Contributed by film2860, 22-Jul-2026.) $)
    com12ALT $p |- ( ps -> ( ph -> ch ) ) $=
      ( wi ax-i1 ax-i4 ax-i2 ax-mp 3syl ) BCBEBEBCECEACEBCBEFCBGABCEEBCECEACEED
      ABCECHIJ $.
  $}

  ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents.  Commuted form
       of ~ mpd .  (Contributed by Lllllllllwith10ls, 25-May-2026.) $)
    mpcom $p |- ( ps -> ( ps -> ch ) ) $=
      ( wi syl ) BABCFDEG $.
  $}

  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction.  (Contributed by Lllllllllwith10ls,
       25-May-2026.) $)
    mpd $p |- ( ph -> ( ph -> ch ) ) $=
      ( com12 mpcom ) BACDABCEFG $.
  $}
  
  $( A modus ponens statement. (Contributed by film2860, 22-July-2026.) $)
  mps $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi ax-i1 ax-i4 syl ) ABACACABCBCABACDBAEF $.

  $( Principle of identity.  (Contributed by Lllllllllwith10ls,
     25-May-2026.) $)
  id $p |- ( ph -> ph )
    $=
    ( wi ax-i1 mpi ) AAAABBAAACAAAABBCD $.


  $( Principle of identity ~ id with antecedent.  (Contributed by NM,
     26-Nov-1995.) $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi id a1i ) BBCABDE $.

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  Deduction form of ~ ax-i1
       and ~ a1i .  (Contributed by NM, 5-Jan-1993.)  (Proof shortened by
       Stefan Allan, 20-Mar-2006.) $)
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi ax-i1 syl ) ABCBEDBCFG $.
  $}

  ${
    2a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing two antecedents.  Two applications of ~ a1d .
       Deduction associated with ~ 2a1 and ~ 2a1i .  (Contributed by BJ,
       10-Aug-2020.) $)
    2a1d $p |- ( ph -> ( ch -> ( th -> ps ) ) ) $=
      ( wi a1d ) ADBFCABDEGG $.
  $}

  ${
    a1i13.1 $e |- ( ps -> th ) $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    a1i13 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi a1d a1i ) BCDFFABDCEGH $.
  $}

  ${
  $( A double form of ~ ax-i1 .  Its associated inference is ~ 2a1i .  Its
     associated deduction is ~ 2a1d .  (Contributed by BJ, 10-Aug-2020.)
     (Proof shortened by Wolf Lammen, 1-Sep-2020.) $)
  2a1 $p |- ( ph -> ( ps -> ( ch -> ph ) ) ) $=
    ( id 2a1d ) AABCADE $.
  $}

  $( Proving that ~ ax-i3 is redundant.  (Contributed by film2860, 22-Jul-2026.) $)
  axi3 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi ax-i2 mps ax-mp syl ) ABCDDBCDCDACDDBACDDABCDCEBBCDCDDBCDCDACDDBACDDDB
    CFBBCDCDACDEGH $.
  
  ${
    $( Analog of ax-2 in classical logic.  (Contributed by Lllllllllwith10ls,
       26-May-2026.) $)
    a2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ( ph
        -> ch ) ) ) ) $=
      ( wi ax-i3 ax-i2 com12 syl ) ABCDDBACDDABDAACDDDABCEABDBACDDAACDDABACDFGH
      $.
  $}

  ${
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference "distributing" an antecedent.  (Contributed by
       Lllllllllwith10ls, 26-May-2026.) $)
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ( ph -> ch ) ) ) $=
      ( wi com12 ax-i2 mpi ) ABEBACEEAACEEABCDFABACEGH $.
  $}


  ${
    imim2i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common antecedents in an implication.  Its associated
       inference is ~ syl .  (Contributed by NM, 28-Dec-1992.) $)
    imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      ( wi ax-i2 com12 ax-mp ) ABECAECBEEDCAEABECBECABFGH $.
  $}


  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    $( Syllogism inference with commutation of antecedents.  (Contributed by
       Lllllllllwith10ls, 26-May-2026.) $)
    sylcom $p |- ( ph -> ( ps -> ( ps -> th ) ) ) $=
      ( wi a2i syl ) ABCGBBDGGEBCDFHI $.
  $}

  ${
    syl5com.1 $e |- ( ph -> ps ) $.
    syl5com.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Syllogism inference with commuted antecedents.  (Contributed by NM,
       24-May-2005.) $)
    syl5com $p |- ( ph -> ( ch -> th ) ) $=
      ( wi com12 syl ) ABCDGECBDFHI $.
  $}

  ${
    syl11.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl11.2 $e |- ( th -> ph ) $.
    $( A syllogism inference.  Commuted form of an instance of ~ syl .
       (Contributed by BJ, 25-Oct-2021.) $)
    syl11 $p |- ( ps -> ( th -> ch ) ) $=
      ( wi syl com12 ) DBCDABCGFEHI $.
  $}

  ${
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  (Contributed by NM,
       27-Dec-1992.)  (Proof shortened by Wolf Lammen, 25-May-2013.) $)
    syl5 $p |- ( ch -> ( ph -> th ) ) $=
      ( syl5com com12 ) ACDABCDEFGH $.
  $}

  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by Lllllllllwith10ls,
       25-May-2026.) $)
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      ( wi ax-i2 a1i ax-i4 ax-mp syl ) ABCGBDGEBCGCDGBDGGBDGBCDHBDGCDGGCDGGCDGB
      DGGBDGGCDGBDGCDGGFIBDGCDGJKLL $.
  $}


  ${
    syl2im.1 $e |- ( ph -> ps ) $.
    syl2im.2 $e |- ( ch -> th ) $.
    syl2im.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Replace two antecedents.  (Contributed by Wolf Lammen, 14-May-2013.) $)
    syl2im $p |- ( ph -> ( ch -> ta ) ) $=
      ( wi syl5 syl ) ABCEIFCDBEGHJK $.

    $( A commuted version of ~ syl2im .  (Contributed by BJ, 20-Oct-2021.) $)
    syl2imc $p |- ( ch -> ( ph -> ta ) ) $=
      ( syl2im com12 ) ACEABCDEFGHIJ $.
  $}


  $( This theorem, sometimes called "Assertion" or "Pon" (for "ponens"), can be
     thought of as a closed form of modus ponens ~ ax-mp .  Theorem *2.27 of
     [WhiteheadRussell] p. 104.  (Contributed by NM, 15-Jul-1993.) $)
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi id com12 ) ABCABABCDE $.


  ${
    imim12i.1 $e |- ( ph -> ps ) $.
    imim12i.2 $e |- ( ch -> th ) $.
    $( Inference joining two implications.  Its associated inference is
       ~ 3syl .  (Contributed by NM, 12-Mar-1993.)  (Proof shortened by Mel L.
       O'Cat, 29-Oct-2011.) $)
    imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $=
      ( wi imim2i syl5 ) ABBCGDECDBFHI $.
  $}

  ${
    imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  Its associated
       inference is ~ syl .  (Contributed by NM, 28-Dec-1992.)  (Proof
       shortened by Wolf Lammen, 4-Aug-2012.) $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      ( id imim12i ) ABCCDCEF $.
  $}

  $( Elimination of a nested antecedent.  Sometimes called "Syll-Simp" since it
     is a syllogism applied to ~ ax-i1 ("Simplification").  (Contributed by
     Wolf Lammen, 9-May-2013.) $)
  jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-i1 imim1i ) BABDCBAEF $.

  ${
    jarri.1 $e |- ( ( ph -> ps ) -> ch ) $.
    $( Inference associated with ~ jarr .  (Contributed by Wolf Lammen,
       20-Sep-2013.) $)
    jarri $p |- ( ps -> ch ) $=
      ( wi ax-i1 syl ) BABECBAFDG $.
  $}

  ${
    syl7.1 $e |- ( ph -> ps ) $.
    syl7.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       third antecedent of the second premise.  (Contributed by NM,
       12-Jan-1993.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( wi id com12 syl syl6 ) CDBEHAEHGABEHEABBEHEHFBEHBEBEHIJKJL $.
  $}


  ${
    syl8.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8.2 $e |- ( th -> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 1-Aug-1994.)
       (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi id syl6 ) ABCDHCEHFCDHCDECDHIGJJ $.
  $}

  ${
    syl9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (Contributed
       by NM, 13-May-1993.)  (Proof shortened by Josh Purinton,
       29-Dec-2000.) $)
    syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi ax-i2 com12 syl ) ABCHDBEHHFDBCHBEHDCEHBCHBEHHGBCHCEHBEHBCEIJKJK $.
  $}

  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Commutation of antecedents.  Swap 2nd and 3rd.  Deduction associated
       with ~ com12 .  (Contributed by NM, 27-Dec-1992.)  (Proof shortened by
       Wolf Lammen, 4-Aug-2012.) $)
    com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( wi pm2.27 syl9 ) ABCDFCDECDGH $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)
    com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $=
      ( wi com23 com12 ) ACBDFABCDEGH $.

    $( Commutation of antecedents.  Swap 1st and 3rd.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $=
      ( com3r com23 ) CABDABCDEFG $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( com3r ) CABDABCDEFF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical negation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

$)


  $( Alias for ~ ax-n1 to be used instead of it for labeling consistency.  Its
     associated inference is ~ con4i and its associated deduction is ~ con4d .
     (Contributed by BJ, 24-Dec-2020.) $)
  con4 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( ax-n1 ) ABC $.


  ${
    con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference associated with ~ con4 .  Its associated inference is ~ mt4 .

       Remark: this can also be proved using ~ notnot followed by ~ nsyl2 ,
       giving a shorter proof but depending on more axioms (namely, ~ ax-i1 and
       ~ ax-i2 ).  (Contributed by NM, 29-Dec-1992.) $)
    con4i $p |- ( ps -> ph ) $=
      ( wn wi con4 ax-mp ) ADBDEBAECABFG $.
    $( $j usage 'con4i' avoids 'ax-1' 'ax-2'; $)
  $}

  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Deduction associated with ~ con4 .  (Contributed by NM, 26-Mar-1995.) $)
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wn wi con4 syl ) ABECEFCBFDBCGH $.
  $}

  ${
    mt4.1 $e |- ph $.
    mt4.2 $e |- ( -. ps -> -. ph ) $.
    $( The rule of modus tollens.  Inference associated with ~ con4i .
       (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4 $p |- ps $=
      ( con4i ax-mp ) ABCBADEF $.
  $}


  ${
    mt4d.1 $e |- ( ph -> ps ) $.
    mt4d.2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
    $( Modus tollens deduction.  Deduction form of ~ mt4 .  (Contributed by NM,
       9-Jun-2006.) $)
    mt4d $p |- ( ph -> ( ph -> ch ) ) $=
      ( con4d mpd ) ABCDACBEFG $.
  $}


  ${
    mt4i.1 $e |- ch $.
    mt4i.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4i $p |- ( ph -> ps ) $=
      ( wn wi con4 com12 ax-mp syl ) ABFCFGBECBFCFGBGDBFCFGCBBCHIJK $.
  $}

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference associated with ~ pm2.21 .
       Its associated inference is ~ pm2.24ii .  (Contributed by NM,
       16-Sep-1993.) $)
    pm2.21i $p |- ( ph -> ps ) $=
      ( wn a1i con4i ) BAADBDCEF $.
  $}

  ${
    pm2.24ii.1 $e |- ph $.
    pm2.24ii.2 $e |- -. ph $.
    $( A contradiction implies anything.  Inference associated with ~ pm2.21i
       and ~ pm2.24i .  (Contributed by NM, 27-Feb-2008.) $)
    pm2.24ii $p |- ps $=
      ( pm2.21i ax-mp ) ABCABDEF $.
    $( $j usage 'pm2.24ii' avoids 'ax-2'; $)
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction associated with ~ pm2.21 .
       (Contributed by NM, 10-Feb-1996.) $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn a1d con4d ) ACBABECEDFG $.
  $}

  $( From a wff and its negation, anything follows.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  Its commuted
     form is ~ pm2.24 and its associated inference is ~ pm2.21i .  (Contributed
     by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen, 14-Sep-2012.) $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn id pm2.21d ) ACABACDE $.

  $( Theorem *2.24 of [WhiteheadRussell] p. 104.  Its associated inference is
     ~ pm2.24i .  Commuted form of ~ pm2.21 .  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn pm2.21 com12 ) ACABABDE $.

  $( Elimination of a nested antecedent.  (Contributed by Wolf Lammen,
     10-May-2013.) $)
  jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $=
    ( wn wi pm2.21 imim1i ) ADABECABFG $.

  ${
    jarli.1 $e |- ( ( ph -> ps ) -> ch ) $.
    $( Inference associated with ~ jarl .  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    jarli $p |- ( -. ph -> ch ) $=
      ( wn wi pm2.21 syl ) AEABFCABGDH $.
  $}


  $( Double negation elimination.  (Contributed by Lllllllllwith10ls,
     26-May-2026.) $)
  notnotr $p |- ( -. -. ph -> ph ) $=
    ( wn wi ax-i1 ax-n1 syl pm2.27 ax-mp ) ABBAAACCACAABBAAACCBBABBCAAACCACABBA
    AACCBBDAAACCBBABBCABAAACCBCAAACCACAAACCBABEAAAACCEFFAAACCAAACCACACAADAAACCA
    GHF $.


  ${
    notnotri.1 $e |- -. -. ph $.
    $( Inference associated with ~ notnotr .  (Contributed by NM, 27-Feb-2008.)
       (Proof shortened by Wolf Lammen, 15-Jul-2021.)  (Revised by Steven
       Nguyen, 27-Dec-2022.) $)
    notnotri $p |- ph $=
      ( wn pm2.21i mt4 ) ACCABACACCCBDE $.
  $}


  $( Double negation introduction.  (Contributed by Lllllllllwith10ls,
     26-May-2026.) $)
  notnot $p |- ( ph -> -. -. ph ) $=
    ( wn notnotr con4i ) ABBAABCD $.

  ${
    notnoti.1 $e |- ph $.
    $( Inference associated with ~ notnot .  (Contributed by NM,
       27-Feb-2008.) $)
    notnoti $p |- -. -. ph $=
      ( wn notnot ax-mp ) AACCBADE $.
  $}


  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 19-Aug-1993.) $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      ( wn notnotr syl5 con4d ) ABECBEEBACEBFDGH $.
  $}

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
     by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    ( wn wi id con2d ) ABCDABABCDEF $.

  $( Contraposition.  (Contributed by Lllllllllwith10ls, 26-May-2026.) $)
  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi notnot imim2i con4d ) ACBDABCBBCCACBEFG $.

  $( Contraposition.  (Contributed by Lllllllllwith10ls, 26-May-2026.) $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn notnotr imim1i con1 syl ) ABCADDBCBDADCADDABAEFADBGH $.

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.) $)
    nsyl3 $p |- ( ch -> -. ph ) $=
      ( wn wi notnotr con3 ax-mp syl ax-n1 ) AFFCFGCAFGAFFACFAHABFCFDCBGBFCFGEC
      BIJKKAFCLJ $.
  $}


  ${
    con2i.a $e |- ( ph -> -. ps ) $.
    $( A contraposition inference.  Its associated inference is ~ mt2 .
       (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Mel L. O'Cat,
       28-Nov-2008.)  (Proof shortened by Wolf Lammen, 13-Jun-2013.) $)
    con2i $p |- ( ps -> -. ph ) $=
      ( id nsyl3 ) ABBCBDE $.
  $}

  ${
    nsyl.1 $e |- ( ph -> -. ps ) $.
    nsyl.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 31-Dec-1993.)
       (Proof shortened by Wolf Lammen, 2-Mar-2013.) $)
    nsyl $p |- ( ph -> -. ch ) $=
      ( nsyl3 con2i ) CAABCDEFG $.
  $}

  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 26-Jun-1994.)
       (Proof shortened by Wolf Lammen, 14-Nov-2023.) $)
    nsyl2 $p |- ( ph -> ch ) $=
      ( wn nsyl3 con4i ) CAABCFDEGH $.
  $}

  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 27-Dec-1992.) $)
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      ( wn notnot syl6 con4d ) ABCEABECCEEDCFGH $.
  $}


  ${
    con1i.1 $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  Inference associated with ~ con1 .
       (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Mel L. O'Cat,
       28-Nov-2008.)  (Proof shortened by Wolf Lammen, 19-Jun-2013.) $)
    con1i $p |- ( -. ps -> ph ) $=
      ( wn id nsyl2 ) BDBABDECF $.
  $}


  ${
    pm2.24i.1 $e |- ph $.
    $( Inference associated with ~ pm2.24 .  Its associated inference is
       ~ pm2.24ii .  (Contributed by NM, 20-Aug-2001.) $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      ( wn a1i con1i ) BAABDCEF $.
  $}

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction form of ~ pm2.24 .  (Contributed by NM, 30-Jan-2006.) $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wn a1d con1d ) ACBABCEDFG $.
  $}


  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction.  Deduction form of ~ con3 .  (Contributed by
       NM, 10-Jan-1993.) $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      ( wn notnotr syl5 con1d ) ABECBEEBACBFDGH $.
  $}

  ${
    con3i.a $e |- ( ph -> ps ) $.
    $( A contraposition inference.  Inference associated with ~ con3 .  Its
       associated inference is ~ mto .  (Contributed by NM, 3-Jan-1993.)
       (Proof shortened by Wolf Lammen, 20-Jun-2013.) $)
    con3i $p |- ( -. ps -> -. ph ) $=
      ( wn id nsyl ) BDBABDECF $.
  $}

  $( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives (see {TODO} pm3.2 ).  (Contributed by NM, 29-Dec-1992.)
     (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    ( wn wi pm2.27 con2d ) AABCDBABCEF $.


  ${
    con3rr3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)
    con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $=
      ( wn con3d com12 ) ACEBEABCDFG $.
  $}

  ${
    nsyli.1 $e |- ( ph -> ( ps -> ch ) ) $.
    nsyli.2 $e |- ( th -> -. ch ) $.
    $( A negated syllogism inference.  (Contributed by NM, 3-May-1994.) $)
    nsyli $p |- ( ph -> ( th -> -. ps ) ) $=
      ( wn con3d syl5 ) DCGABGFABCEHI $.
  $}

  ${
    nsyl4.1 $e |- ( ph -> ps ) $.
    nsyl4.2 $e |- ( -. ph -> ch ) $.
    $( A negated syllogism inference.  (Contributed by NM, 15-Feb-1996.) $)
    nsyl4 $p |- ( -. ch -> ps ) $=
      ( wn con1i syl ) CFABACEGDH $.

    $( A negated syllogism inference.  (Contributed by Wolf Lammen,
       20-May-2024.) $)
    nsyl5 $p |- ( -. ps -> ch ) $=
      ( nsyl4 con1i ) CBABCDEFG $.
  $}


  $( Theorem joining the consequents of two premises.  Theorem 8 of [Margaris]
     p. 60.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.) $)
  jcn $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    ( wi pm2.27 con3d ) AABCBABDE $.

  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An importation inference.  (Contributed by NM, 29-Dec-1992.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2013.) $)
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      ( wn wi con3rr3 con1i ) CABEFABCDGH $.
  $}

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (Contributed by NM, 29-Dec-1992.)  (Proof
       shortened by Mel L. O'Cat, 28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm3.2im syl6 ) ABABEFECABGDH $.
  $}

  $( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    ( idd impi ) ABBABCD $.

  $( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 21-Jul-2012.) $)
  simplim $p |- ( -. ( ph -> ps ) -> ph ) $=
    ( wi pm2.21 con1i ) AABCABDE $.

  $( General instance of Theorem *2.5 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf Lammen,
     9-Oct-2012.) $)
  pm2.5g $p |- ( -. ( ph -> ps ) -> ( -. ph -> ch ) ) $=
    ( wi wn simplim pm2.24d ) ABDEACABFG $.

  $( Theorem *2.5 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $=
    ( pm2.5g ) ABBC $.

  $( Contrapositive of ~ ax-i1 .  (Contributed by BJ, 28-Oct-2023.) $)
  conax1 $p |- ( -. ( ph -> ps ) -> -. ps ) $=
    ( wi ax-i1 con3i ) BABCBADE $.

  $( Weakening of ~ conax1 .  General instance of ~ pm2.51 and of ~ pm2.52 .
     (Contributed by BJ, 28-Oct-2023.) $)
  conax1k $p |- ( -. ( ph -> ps ) -> ( ch -> -. ps ) ) $=
    ( wi wn conax1 a1d ) ABDEBECABFG $.

  $( Theorem *2.51 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    ( conax1k ) ABAC $.

  $( Theorem *2.52 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
  pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    ( wn conax1k ) ABACD $.

  $( A general instance of Theorem *2.521 of [WhiteheadRussell] p. 107.
     (Contributed by BJ, 28-Oct-2023.) $)
  pm2.521g $p |- ( -. ( ph -> ps ) -> ( ps -> ch ) ) $=
    ( wi wn conax1 pm2.21d ) ABDEBCABFG $.

  $( A general instance of Theorem *2.521 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf Lammen,
     8-Oct-2012.) $)
  pm2.521g2 $p |- ( -. ( ph -> ps ) -> ( ch -> ph ) ) $=
    ( wi wn simplim a1d ) ABDEACABFG $.

  $( Theorem *2.521 of [WhiteheadRussell] p. 107.  Instance of ~ pm2.521g and
     of ~ pm2.521g2 .  (Contributed by NM, 3-Jan-2005.) $)
  pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $=
    ( pm2.521g ) ABAC $.


  ${
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens.  Inference associated with ~ con2i .
       (Contributed by NM, 19-Aug-1993.)  (Proof shortened by Wolf Lammen,
       10-Sep-2013.) $)
    mt2 $p |- -. ph $=
      ( wn notnotr syl con4i ax-mp ) BAECAEBAEEABEAFDGHI $.
  $}


  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens.  The rule says, "if ` ps ` is not true, and
       ` ph ` implies ` ps ` , then ` ph ` must also be not true".  Modus
       tollens is short for "modus tollendo tollens", a Latin phrase that means
       "the mode that by denying denies" - remark in [Sanford] p. 39.  It is
       also called denying the consequent.  Modus tollens is closely related to
       modus ponens ~ ax-mp .  Note that this rule is also valid in
       intuitionistic logic.  Inference associated with ~ con3i .  (Contributed
       by NM, 19-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    mto $p |- -. ph $=
      ( wn notnot syl mt2 ) ABECABBEEDBFGH $.
  $}


  ${
    mtoi.1 $e |- -. ch $.
    mtoi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 5-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mtoi $p |- ( ph -> -. ps ) $=
      ( wn wi con3d com12 ax-mp ) CFABFGDACFBFABCEHIJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Definition ~ df-bi in this section is our first definition, which
  introduces and defines the biconditional connective ` <-> ` used to denote
  logical equivalence.  We define a wff of the form ` ( ph <-> ps ) ` as an
  abbreviation for ` -. ( ( -. ( ( ph <-> ps ) -> -. ( ( -. ( ph -> ps ) ->
  -. ( ps -> ph ) ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( -. ( ph -> ps )
  -> -. ( ps -> ph ) ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) -> -. ( -.
  ( ( -. ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ps -> ph ) ) ->
  ( ph <-> ps ) ) ) ` .

  Unlike most traditional developments, we have chosen not to have a separate
  symbol such as "Df." to mean "is defined as".  Instead, we will later use the
  biconditional connective for this purpose ( {TODO} df-an is its first use),
  as it
  allows to use logic to manipulate definitions directly.  This greatly
  simplifies many proofs since it eliminates the need for a separate mechanism
  for introducing and eliminating definitions.

  A note on definitions: definitions are required to be eliminable (that is, a
  theorem stated in terms of the defined symbol can also be stated without it)
  and conservative (that is, a theorem whose statement does not contain the
  defined symbol can be proved without using that definition).  This means that
  a definition does not increase the expressive power nor the deductive power,
  respectively, of a theory.  On the other hand, definitions are often useful
  to write shorter proofs, so in (i)set.mm we will generally not try to avoid
  them.  This is why, for instance, some theorems which do not contain
  disjunction in their statement are placed after the section on disjunction
  because a shorter proof using disjunction is possible.

$)

  $( Declare the biconditional connective. $)
  $c <-> $.  $( Bidirectional arrow (read:  "if and only if" or
                "is logically equivalent to") $)

  $( Extend wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( Define the biconditional (logical "iff" or "if and only if"), also called
     biimplication.  (Contributed by Lllllllllwith10ls, 28-May-2026.) $)
  df-bi $a |- -. ( ( -. ( ( ph <-> ps ) -> -. ( ( -. ( ph -> ps ) ->
  -. ( ps -> ph ) ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( -. ( ph -> ps )
  -> -. ( ps -> ph ) ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) -> -. ( -.
  ( ( -. ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ps -> ph ) ) ->
  ( ph <-> ps ) ) ) $.

  $( $j justification 'bijust' for 'df-bi'; $)

  ${
    impandli.1 $e |- -. ( ( -. ph -> -. ps ) -> -. ps ) $.
    $( And defined by implication (Contributed by Lllllllllwith10ls,
       28-May-2026.) $)
    impandli $p |- ph $=
      ( wn wi pm2.27 notnot syl mt4 ) ADBDEBDEDACADADBDEBDEADBDEBDEDDADBDFADBDE
      BDEGHI $.
  $}


  ${
    impandri.1 $e |- -. ( ( -. ph -> -. ps ) -> -. ps ) $.
    $( And defined by implication (Contributed by Lllllllllwith10ls,
       28-May-2026.) $)
    impandri $p |- ps $=
      ( wn wi notnot jarri mt4 ) ADBDEBDEDBCADBDEBDADBDEBDEDDADBDEBDEFGH $.
  $}

  $( And defined by implication (Contributed by Lllllllllwith10ls,
     28-May-2026.) $)
  impandl $p |- ( -. ( ( -. ph -> -. ps ) -> -. ps ) -> ph ) $=
    ( wn wi pm2.27 con1i ) AACBCDBCDACBCEF $.


  $( And defined by implication (Contributed by Lllllllllwith10ls,
     28-May-2026.) $)
  impandr $p |- ( -. ( ( -. ph -> -. ps ) -> -. ps ) -> ps ) $=
    ( wn wi simprim ) ACBCDBE $.


  $( And defined by implication (Contributed by Lllllllllwith10ls,
     29-May-2026.) $)
  impand $p |- ( ph -> ( ps -> -. ( ( -. ph -> -. ps ) -> -. ps ) ) ) $=
    ( wn wi notnot pm2.24 imim1i con3rr3 syl ) AACCBACBCDBCDCDAEBACBCDBCDACBBCC
    ACBCDBCDACDBEACBCDBCDABCAACBCDBCABCFGHIHI $.


  ${
    impandd.1 $e |- ( ph -> ps ) $.
    impandd.2 $e |- ( ph -> ch ) $.
    $( And defined by implication (Contributed by Lllllllllwith10ls,
       31-May-2026.) $)
    impandd $p |- ( ph -> -. ( ( -. ps -> -. ch ) -> -. ch ) ) $=
      ( wn notnoti notnot con3 ax-i4 con3i imim1i syl11 ax-i1 syl6 syl7 con3rr3
      wi mpi syl mtoi ) ABFCFRCFRABRFABRDGAAFFBFCFRCFRABRFRAHBFCFRCFRABRAFBFCFR
      CFRACRABRAFREABRBFAFRBFCFRCFRACRAFABICFAFRBFCFRCFRBFAFRAFRACRCFAFRBFCFRCF
      RAFBFAFRAFRAFCFRCFRCFAFRAFBFCFRCFRAFCFJAFCFRBFCFRCFBFAFCFABDKLLMAFBFAFRNO
      ACIMPSQTUA $.
  $}

  $( Property of the biconditional connective.  (Contributed by
     Lllllllllwith10ls, 28-May-2026.) $)
  impbia $p |- ( -. ( ( -. ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ps -> ph )
  ) -> ( ph <-> ps ) ) $=
    ( wb wi wn df-bi impandri ) ABCABDEBADEDBADEDEDABDEBADEDBADEDEABCDABFG $.

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  impbi $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wn wb impand impbia syl6 ) ABCBACABCDBACDCBACDCDABEABCBACFABGH $.

  ${
    impbid21d.1 $e |- ( ps -> ( ch -> th ) ) $.
    impbid21d.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)
    impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb impbi syl2imc ) BCDGADCGCDHEFCDIJ $.
  $}

  ${
    impbid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by
       Lllllllllwith10ls, 31-May-2026.) $)
    impbid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi wn wb impandd impbia syl ) ABCFGCBFGFCBFGFGBCHABCFCBFDEIBCJK $.
  $}


  ${
    impbii.1 $e |- ( ph -> ps ) $.
    impbii.2 $e |- ( ps -> ph ) $.
    $( Infer an equivalence from an implication and its converse.  Inference
       associated with ~ impbi .  (Contributed by NM, 29-Dec-1992.) $)
    impbii $p |- ( ph <-> ps ) $=
      ( wi wb impbi mp2 ) ABEBAEABFCDABGH $.
  $}


  $( Property of the biconditional connective.  (Contributed by
     Lllllllllwith10ls, 29-May-2026.) $)
  biimpa $p |- ( ( ph <-> ps ) -> -. ( ( -. ( ph -> ps ) ->
  -. ( ps -> ph ) ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn df-bi impandli ) ABCABDEBADEDBADEDEDABDEBADEDBADEDEABCDABFG $.


  $( Property of the biconditional connective.  (Contributed by
     Lllllllllwith10ls, 29-May-2026.) $)
  biimp $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi wn biimpa impandl syl ) ABCABDEBADEDBADEDEABDABFABDBADGH $.

  ${
    biimpi.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence.  Inference associated
       with ~ biimp .  (Contributed by NM, 29-Dec-1992.) $)
    biimpi $p |- ( ph -> ps ) $=
      ( wb wi biimp ax-mp ) ABDABECABFG $.
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by NM, 3-Jan-1993.) $)
    sylbi $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCABDFEG $.
  $}

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by NM, 3-Jan-1993.) $)
    sylib $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCDBCEFG $.
  $}

  ${
    sylbb.1 $e |- ( ph <-> ps ) $.
    sylbb.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 30-Mar-2019.) $)
    sylbb $p |- ( ph -> ch ) $=
      ( biimpi sylbi ) ABCDBCEFG $.
  $}

  $( Property of the biconditional connective.  (Contributed by
     Lllllllllwith10ls, 29-May-2026.) $)
  biimpr $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi wn biimpa ax-i1 nsyl2 ) ABCABDEBADEDBADEDBADABFBADEABDEBADEDGH $.

  $( Commutative law for the biconditional.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
  bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb biimpr biimp impbid ) ABCBAABDABEF $.

  $( Commutative law for the biconditional.  Theorem *4.21 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 11-May-1993.) $)
  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    ( wb bicom1 impbii ) ABCBACABDBADE $.

  ${
    bicomd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Commute two sides of a biconditional in a deduction.  (Contributed by
       NM, 14-May-1993.) $)
    bicomd $p |- ( ph -> ( ch <-> ps ) ) $=
      ( wb bicom sylib ) ABCECBEDBCFG $.
  $}

  ${
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence.  (Contributed by
       NM, 3-Jan-1993.) $)
    bicomi $p |- ( ps <-> ph ) $=
      ( wb bicom1 ax-mp ) ABDBADCABEF $.
  $}

  ${
    impbid1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid1.2 $e |- ( ch -> ps ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.) $)
    impbid1 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi a1i impbid ) ABCDCBFAEGH $.
  $}

  ${
    impbid2.1 $e |- ( ps -> ch ) $.
    impbid2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.)  (Proof shortened by Wolf Lammen, 27-Sep-2013.) $)
    impbid2 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( impbid1 bicomd ) ACBACBEDFG $.
  $}

  ${
    impcon4bid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impcon4bid.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)
    impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( con4d impbid ) ABCDABCEFG $.
  $}

  ${
    biimpri.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence.  Inference
       associated with ~ biimpr .  (Contributed by NM, 29-Dec-1992.)  (Proof
       shortened by Wolf Lammen, 16-Sep-2013.) $)
    biimpri $p |- ( ps -> ph ) $=
      ( bicomi biimpi ) BAABCDE $.
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce an implication from a logical equivalence.  Deduction associated
       with ~ biimp and ~ biimpi .  (Contributed by NM, 11-Jan-1993.) $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb wi biimp syl ) ABCEBCFDBCGH $.
  $}

  ${
    mpbi.min $e |- ph $.
    mpbi.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 11-May-1993.) $)
    mpbi $p |- ps $=
      ( biimpi ax-mp ) ABCABDEF $.
  $}

  ${
    mpbir.min $e |- ps $.
    mpbir.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 28-Dec-1992.) $)
    mpbir $p |- ph $=
      ( biimpri ax-mp ) BACABDEF $.
  $}

  ${
    mpbii.min $e |- ps $.
    mpbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 16-May-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mpbii $p |- ( ph -> ch ) $=
      ( biimpd mpi ) ABCDABCEFG $.
  $}

  ${
    sylibr.1 $e |- ( ph -> ps ) $.
    sylibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       NM, 3-Jan-1993.) $)
    sylibr $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCDCBEFG $.
  $}

  ${
    sylbir.1 $e |- ( ps <-> ph ) $.
    sylbir.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by NM, 3-Jan-1993.) $)
    sylbir $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCBADFEG $.
  $}

  ${
    sylbbr.1 $e |- ( ph <-> ps ) $.
    sylbbr.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.

       Note on the various syllogism-like statements in set.mm.  The
       hypothetical syllogism ~ syl infers an implication from two implications
       (and there are ~ 3syl and ~ 4syl for chaining more inferences).  There
       are four inferences inferring an implication from one implication and
       one biconditional: ~ sylbi , ~ sylib , ~ sylbir , ~ sylibr ; four
       inferences inferring an implication from two biconditionals: ~ sylbb ,
       ~ sylbbr , ~ sylbb1 , ~ sylbb2 ; four inferences inferring a
       biconditional from two biconditionals: ~ bitri , ~ bitr2i , ~ bitr3i ,
       ~ bitr4i (and more for chaining more biconditionals).  There are also
       closed forms and deduction versions of these, like, among many others,
       ~ syl5 , ~ syl6 , ~ bitrid , ~ bitrdi and variants.  (Contributed by BJ,
       21-Apr-2019.) $)
    sylbbr $p |- ( ch -> ph ) $=
      ( biimpri sylibr ) CBABCEFDG $.
  $}

  ${
    sylbb1.1 $e |- ( ph <-> ps ) $.
    sylbb1.2 $e |- ( ph <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 21-Apr-2019.) $)
    sylbb1 $p |- ( ps -> ch ) $=
      ( biimpri sylib ) BACABDFEG $.
  $}

  ${
    sylbb2.1 $e |- ( ph <-> ps ) $.
    sylbb2.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 21-Apr-2019.) $)
    sylbb2 $p |- ( ph -> ch ) $=
      ( biimpri sylbi ) ABCDCBEFG $.
  $}

  ${
    biimtrid.1 $e |- ( ph <-> ps ) $.
    biimtrid.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  (Contributed by NM, 12-Jan-1993.) $)
    biimtrid $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpi syl5 ) ABCDABEGFH $.
  $}

  ${
    biimtrrid.1 $e |- ( ps <-> ph ) $.
    biimtrrid.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 21-Jun-1993.) $)
    biimtrrid $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpri syl5 ) ABCDBAEGFH $.
  $}

  ${
    imbitrid.1 $e |- ( ph -> ps ) $.
    imbitrid.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 12-Jan-1993.) $)
    imbitrid $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpd syl5 ) ABCDECBDFGH $.

    $( A mixed syllogism inference.  (Contributed by NM, 19-Jun-2007.) $)
    syl5ibcom $p |- ( ph -> ( ch -> th ) ) $=
      ( imbitrid com12 ) CADABCDEFGH $.
  $}

  ${
    imbitrrid.1 $e |- ( ph -> th ) $.
    imbitrrid.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 3-Apr-1994.) $)
    imbitrrid $p |- ( ch -> ( ph -> ps ) ) $=
      ( bicomd imbitrid ) ADCBECBDFGH $.

    $( A mixed syllogism inference.  (Contributed by NM, 20-Jun-2007.) $)
    syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $=
      ( imbitrrid com12 ) CABABCDEFGH $.
  $}

  ${
    biimprd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a converse implication from a logical equivalence.  Deduction
       associated with ~ biimpr and ~ biimpri .  (Contributed by NM,
       11-Jan-1993.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      ( id imbitrrid ) CBACCEDF $.
  $}

  ${
    biimpcd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a commuted implication from a logical equivalence.  (Contributed
       by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimpcd $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5ibcom ) BBACBEDF $.

    $( Deduce a converse commuted implication from a logical equivalence.
       (Contributed by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen,
       20-Dec-2013.) $)
    biimprcd $p |- ( ch -> ( ph -> ps ) ) $=
      ( id syl5ibrcom ) CBACCEDF $.
  $}

  ${
    imbitrdi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imbitrdi.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 21-Jun-1993.) $)
    imbitrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpi syl6 ) ABCDECDFGH $.
  $}

  ${
    imbitrrdi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imbitrrdi.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    imbitrrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpri syl6 ) ABCDEDCFGH $.
  $}

  ${
    biimtrdi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    biimtrdi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 2-Jan-1994.) $)
    biimtrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syl6 ) ABCDABCEGFH $.
  $}

  ${
    biimtrrdi.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    biimtrrdi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    biimtrrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syl6 ) ABCDACBEGFH $.
  $}

  ${
    syl7bi.1 $e |- ( ph <-> ps ) $.
    syl7bi.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A mixed syllogism inference from a doubly nested implication and a
       biconditional.  (Contributed by NM, 14-May-1993.) $)
    syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( biimpi syl7 ) ABCDEABFHGI $.
  $}

  ${
    syl8ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8ib.2 $e |- ( th <-> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM,
       1-Aug-1994.) $)
    syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( biimpi syl8 ) ABCDEFDEGHI $.
  $}

  $( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117.  This is part of Frege's eighth axiom per
     Proposition 54 of [Frege1879] p. 50; see also {TODO} eqid .  (Contributed
     by NM, 2-Jun-1993.) $)
  biid $p |- ( ph <-> ph ) $=
    ( id impbii ) AAABABC $.

  $( Principle of identity with antecedent.  (Contributed by NM,
     25-Nov-1995.) $)
  biidd $p |- ( ph -> ( ps <-> ps ) ) $=
    ( wb biid a1i ) BBCABDE $.

  $( Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ biimp -like version of the xor-connective.
     This theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .
     (Contributed by Wolf Lammen, 12-May-2013.) $)
  pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $=
    ( ax-i1 impbid21d ) ABABBACABCD $.

  ${
    2th.1 $e |- ph $.
    2th.2 $e |- ps $.
    $( Two truths are equivalent.  (Contributed by NM, 18-Aug-1993.) $)
    2th $p |- ( ph <-> ps ) $=
      ( a1i impbii ) ABBADEABCEF $.
  $}


  ${
    2thd.1 $e |- ( ph -> ps ) $.
    2thd.2 $e |- ( ph -> ch ) $.
    $( Two truths are equivalent.  Deduction form.  (Contributed by
       Lllllllllwith10ls, 18-Jun-2026.) $)
    2thd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( a1d impbid ) ABCACBEFABCDFG $.
  $}

  $( Two self-implications (see ~ id ) are equivalent.  This theorem, rather
     trivial in our axiomatization, is (the biconditional form of) a standard
     axiom for monothetic BCI logic.  This is the most general theorem of which
     {TODO} trujust is an instance.  Relatedly, this would be the justification
     theorem if the definition of ` T. ` were {TODO} dftru2 .  (Contributed by
     BJ, 7-Sep-2022.) $)
  monothetic $p |- ( ( ph -> ph ) <-> ( ps -> ps ) ) $=
    ( wi id 2th ) AACBBCADBDE $.


  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen, 13-Oct-2012.) $)
    bitri $p |- ( ph <-> ch ) $=
      ( sylbb sylbbr impbii ) ACABCDEFABCDEGH $.
  $}

  ${
    bitr2i.1 $e |- ( ph <-> ps ) $.
    bitr2i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 12-Mar-1993.) $)
    bitr2i $p |- ( ch <-> ph ) $=
      ( bitri bicomi ) ACABCDEFG $.
  $}

  ${
    bitr3i.1 $e |- ( ps <-> ph ) $.
    bitr3i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 2-Jun-1993.) $)
    bitr3i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCBADFEG $.
  $}

  ${
    bitr4i.1 $e |- ( ph <-> ps ) $.
    bitr4i.2 $e |- ( ch <-> ps ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 3-Jan-1993.) $)
    bitr4i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCDCBEFG $.
  $}

  $( Register '<->' as an equality for its type (wff). $)
  $( $j
    equality 'wb' from 'biid' 'bicomi' 'bitri';
    definition 'dfbi1' for 'wb';
  $)


  ${
    bitrdi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrdi.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by
       Lllllllllwith10ls, 18-Jun-2026.) $)
    bitrdi $p |- ( ph -> ( ps <-> th ) ) $=
      ( biimpi biimtrdi biimpri imbitrrid impbid ) ABDABCDECDFGHDBACCDFIEJK $.
  $}

  ${
    bitrid.1 $e |- ( ph <-> ps ) $.
    bitrid.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       12-Mar-1993.) $)
    bitrid $p |- ( ch -> ( ph <-> th ) ) $=
      ( bicomd bicomi bitrdi ) CDACDBACBDFGABEHIG $.
  $}

  ${
    bitr2id.1 $e |- ( ph <-> ps ) $.
    bitr2id.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       1-Aug-1993.) $)
    bitr2id $p |- ( ch -> ( th <-> ph ) ) $=
      ( bitrid bicomd ) CADABCDEFGH $.
  $}

  ${
    bitr3id.1 $e |- ( ps <-> ph ) $.
    bitr3id.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr3id $p |- ( ch -> ( ph <-> th ) ) $=
      ( bicomi bitrid ) ABCDBAEGFH $.
  $}

  ${
    bitr3di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3di.2 $e |- ( ps <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    bitr3di $p |- ( ph -> ( ch <-> th ) ) $=
      ( bicomi bitr2id ) DBACBDFGEH $.
  $}

  ${
    bitr2di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2di.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr2di $p |- ( ph -> ( th <-> ps ) ) $=
      ( bitrdi bicomd ) ABDABCDEFGH $.
  $}

  ${
    bitr4di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4di.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       12-Mar-1993.) $)
    bitr4di $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi bitrdi ) ABCDEDCFGH $.
  $}

  ${
    bitr4id.2 $e |- ( ps <-> ch ) $.
    bitr4id.1 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    bitr4id $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi bitr2di ) ADCBFBCEGH $.
  $}

  ${
    3imtr3.1 $e |- ( ph -> ps ) $.
    3imtr3.2 $e |- ( ph <-> ch ) $.
    3imtr3.3 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication.  (Contributed by NM, 10-Aug-1994.) $)
    3imtr3i $p |- ( ch -> th ) $=
      ( sylbir sylib ) CBDCABFEHGI $.
  $}

  ${
    3imtr4.1 $e |- ( ph -> ps ) $.
    3imtr4.2 $e |- ( ch <-> ph ) $.
    3imtr4.3 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication.  (Contributed by NM, 3-Jan-1993.) $)
    3imtr4i $p |- ( ch -> th ) $=
      ( sylbi sylibr ) CBDCABFEHGI $.
  $}

  ${
    3imtr3g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3g.2 $e |- ( ps <-> th ) $.
    3imtr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr3g $p |- ( ph -> ( th -> ta ) ) $=
      ( biimtrrid imbitrdi ) ADCEDBACGFIHJ $.
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      ( biimtrid imbitrrdi ) ADCEDBACGFIHJ $.
  $}

  ${
    3bitri.1 $e |- ( ph <-> ps ) $.
    3bitri.2 $e |- ( ps <-> ch ) $.
    3bitri.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 3-Jan-1993.) $)
    3bitri $p |- ( ph <-> th ) $=
      ( bitri ) ABDEBCDFGHH $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitrri $p |- ( th <-> ph ) $=
      ( bitr2i bitr3i ) DCAGABCEFHI $.
  $}

  ${
    3bitr2i.1 $e |- ( ph <-> ps ) $.
    3bitr2i.2 $e |- ( ch <-> ps ) $.
    3bitr2i.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2i $p |- ( ph <-> th ) $=
      ( bitr4i bitri ) ACDABCEFHGI $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2ri $p |- ( th <-> ph ) $=
      ( bitr4i bitr2i ) ACDABCEFHGI $.
  $}

  ${
    3bitr3i.1 $e |- ( ph <-> ps ) $.
    3bitr3i.2 $e |- ( ph <-> ch ) $.
    3bitr3i.3 $e |- ( ps <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 19-Aug-1993.) $)
    3bitr3i $p |- ( ch <-> th ) $=
      ( bitr3i bitri ) CBDCABFEHGI $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 21-Jun-1993.) $)
    3bitr3ri $p |- ( th <-> ch ) $=
      ( bitr3i ) DBCGBACEFHH $.
  $}

  ${
    3bitr4i.1 $e |- ( ph <-> ps ) $.
    3bitr4i.2 $e |- ( ch <-> ph ) $.
    3bitr4i.3 $e |- ( th <-> ps ) $.
    $( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence.  (Contributed by NM, 3-Jan-1993.) $)
    3bitr4i $p |- ( ch <-> th ) $=
      ( bitr4i bitri ) CADFABDEGHI $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 2-Sep-1995.) $)
    3bitr4ri $p |- ( th <-> ch ) $=
      ( bitr4i bitr2i ) CADFABDEGHI $.
  $}

  ${
    3bitr3g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3g.2 $e |- ( ps <-> th ) $.
    3bitr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 4-Jun-1995.) $)
    3bitr3g $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr3id bitrdi ) ADCEDBACGFIHJ $.
  $}


  $( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117.
     (Contributed by NM, 3-Jan-1993.) $)
  notnotb $p |- ( ph <-> -. -. ph ) $=
    ( wn notnot notnotr impbii ) AABBACADE $.

  $( A biconditional form of contraposition.  Theorem *4.1 of
     [WhiteheadRussell] p. 116.  (Contributed by NM, 11-May-1993.) $)
  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    ( wi wn con3 con4 impbii ) ABCBDADCABEBAFG $.

  ${
    con4bid.1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 21-May-1994.) $)
    con4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wn biimprd con4d biimpd impcon4bid ) ABCACBABECEDFGABECEDHI $.
  $}

  ${
    notbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction negating both sides of a logical equivalence.  (Contributed by
       NM, 21-May-1994.) $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      ( wn notnotb 3bitr3g con4bid ) ABECEABCBEECEEDBFCFGH $.
  $}

  $( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 21-May-1994.)  (Proof shortened by Wolf Lammen, 12-Jun-2013.) $)
  notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $=
    ( wb wn id notbid con4bid impbii ) ABCADBDCABCABABCEFADBDCABADBDCEGH $.

  ${
    notbii.1 $e |- ( ph <-> ps ) $.
    $( Negate both sides of a logical equivalence.  (Contributed by NM,
       3-Jan-1993.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      ( wb wn notbi mpbi ) ABDAEBEDCABFG $.

    $( Theorem notbii is the congruence law for negation. $)
    $( $j congruence 'notbii'; $)
  $}


  ${
    con4bii.1 $e |- ( -. ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 21-May-1994.) $)
    con4bii $p |- ( ph <-> ps ) $=
      ( wb wn notbi mpbir ) ABDAEBEDCABFG $.
  $}

  ${
    mtbi.1 $e |- -. ph $.
    mtbi.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mtbi $p |- -. ps $=
      ( biimpri mto ) BACABDEF $.
  $}

  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       14-Oct-2012.) $)
    mtbir $p |- -. ph $=
      ( bicomi mtbi ) BACABDEF $.
  $}

  ${
    mtbii.min $e |- -. ps $.
    mtbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 27-Nov-1995.) $)
    mtbii $p |- ( ph -> -. ch ) $=
      ( biimprd mtoi ) ACBDABCEFG $.
  $}

  ${
    mtbiri.min $e |- -. ch $.
    mtbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 24-Aug-1995.) $)
    mtbiri $p |- ( ph -> -. ps ) $=
      ( biimpd mtoi ) ABCDABCEFG $.
  $}

  ${
    sylnib.1 $e |- ( ph -> -. ps ) $.
    sylnib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnib $p |- ( ph -> -. ch ) $=
      ( biimpri nsyl ) ABCDBCEFG $.
  $}

  ${
    sylnibr.1 $e |- ( ph -> -. ps ) $.
    sylnibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       Wolf Lammen, 16-Dec-2013.) $)
    sylnibr $p |- ( ph -> -. ch ) $=
      ( bicomi sylnib ) ABCDCBEFG $.
  $}

  ${
    sylnbi.1 $e |- ( ph <-> ps ) $.
    sylnbi.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnbi $p |- ( -. ph -> ch ) $=
      ( wn notbii sylbi ) AFBFCABDGEH $.
  $}

  ${
    sylnbir.1 $e |- ( ps <-> ph ) $.
    sylnbir.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnbir $p |- ( -. ph -> ch ) $=
      ( bicomi sylnbi ) ABCBADFEG $.
  $}

  ${
    xchnxbi.1 $e |- ( -. ph <-> ps ) $.
    xchnxbi.2 $e |- ( ph <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbi $p |- ( -. ch <-> ps ) $=
      ( wn notbii bitr3i ) CFAFBACEGDH $.
  $}

  ${
    xchnxbir.1 $e |- ( -. ph <-> ps ) $.
    xchnxbir.2 $e |- ( ch <-> ph ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbir $p |- ( -. ch <-> ps ) $=
      ( bicomi xchnxbi ) ABCDCAEFG $.
  $}

  ${
    xchbinx.1 $e |- ( ph <-> -. ps ) $.
    xchbinx.2 $e |- ( ps <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinx $p |- ( ph <-> -. ch ) $=
      ( wn notbii bitri ) ABFCFDBCEGH $.
  $}

  ${
    xchbinxr.1 $e |- ( ph <-> -. ps ) $.
    xchbinxr.2 $e |- ( ch <-> ps ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinxr $p |- ( ph <-> -. ch ) $=
      ( bicomi xchbinx ) ABCDCBEFG $.
  $}

  ${
    imbi2i.1 $e |- ( ph <-> ps ) $.
    $( Introduce an antecedent to both sides of a logical equivalence.  This
       and the next three rules are useful for building up wff's around a
       definition, in order to make use of the definition.  (Contributed by
       Lllllllllwith10ls, 18-Jun-2026.) $)
    imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
      ( wi biimpi imim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.
  $}


  ${
    bibi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a biconditional to the left in an equivalence.
       (Contributed by NM, 26-May-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.)  (Proof shortened by Wolf Lammen, 16-May-2013.) $)
    bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $=
      ( wb id bitrdi bitr4di impbii ) CAECBECAECABCAEFDGCBECBACBEFDHI $.

    $( Inference adding a biconditional to the right in an equivalence.
       (Contributed by NM, 26-May-1993.) $)
    bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb bicom bibi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.

    ${
      bibi12i.2 $e |- ( ch <-> th ) $.
      $( The equivalence of two equivalences.  (Contributed by NM,
         26-May-1993.) $)
      bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $=
        ( wb bibi2i bibi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
    $}
  $}


  $( Theorem *4.84 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $=
    ( wb wi biimpr ax-i2 syl biimp impbid ) ABDACEBCEABDBAEACEBCEEABFBACGHABDAB
    EBCEACEEABIABCGHJ $.

  $( Theorem *4.85 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
  imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $=
    ( wb wi biimp ax-i2 syl5com biimpr impbid ) ABDCAECBEABDABECAECBEABFCABGHAB
    DBAECBECAEABICBAGHJ $.

  ${
    imbi1i.1 $e |- ( ph <-> ps ) $.
    $( Introduce a consequent to both sides of a logical equivalence.
       (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
      ( wb wi imbi1 ax-mp ) ABEACFBCFEDABCGH $.
  $}

  ${
    imbi12i.1 $e |- ( ph <-> ps ) $.
    imbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences to form equivalence of implications.
       (Contributed by NM, 1-Aug-1993.) $)
    imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
      ( wi biimpri biimpi imim12i impbii ) ACGBDGBACDABEHCDFIJABDCABEICDFHJK $.

    $( Theorem imbi12i is the congruence law for implication. $)
    $( $j congruence 'imbi12i'; $)
  $}

  $( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 15-Apr-1995.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
  con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $=
    ( wn wb notbi notnotb bibi2i bicom 3bitr2i ) ABCDACBCCDACBDBACDABCEBBCCACBF
    GACBHI $.

  ${
    con2bid.1 $e |- ( ph -> ( ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 15-Apr-1995.) $)
    con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $=
      ( wn wb con2bi sylibr ) ABCEFCBEFDCBGH $.
  $}

  ${
    con1bid.1 $e |- ( ph -> ( -. ps <-> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 9-Oct-1999.) $)
    con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $=
      ( wn bicomd con2bid ) ABCEACBABECDFGF $.
  $}

  ${
    con1bii.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 12-Mar-1993.)  (Proof
       shortened by Wolf Lammen, 13-Oct-2012.) $)
    con1bii $p |- ( -. ps <-> ph ) $=
      ( wn notnotb xchbinx bicomi ) ABDAADBAECFG $.
  $}

  ${
    con2bii.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 12-Mar-1993.) $)
    con2bii $p |- ( ps <-> -. ph ) $=
      ( wn notnotb xchbinxr ) BBDABECF $.
  $}

  $( Contraposition.  Bidirectional version of ~ con1 .  (Contributed by NM,
     3-Jan-1993.) $)
  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    ( wn wi con1 impbii ) ACBDBCADABEBAEF $.

  $( Contraposition.  Bidirectional version of ~ con2 .  (Contributed by NM,
     12-Mar-1993.) $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    ( wn wi con2 impbii ) ABCDBACDABEBAEF $.

  $( A wff is equivalent to itself with true antecedent.  (Contributed by NM,
     28-Jan-1996.) $)
  biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $=
    ( wi ax-i1 pm2.27 impbid2 ) ABABCBADABEF $.

  $( Theorem *5.5 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $=
    ( wi biimt bicomd ) ABABCABDE $.

  ${
    a1bi.1 $e |- ph $.
    $( Inference introducing a theorem as an antecedent.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      ( wi wb biimt ax-mp ) ABABDECABFG $.
  $}

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Nov-2012.) $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      ( wn wi a1bi con2b bitri ) BDABDEBADEABDCFABGH $.
  $}

  $( Modus-tollens-like theorem.  (Contributed by NM, 7-Apr-2001.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2012.) $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    ( wn wi biimt con34b bitr4di ) ACBCACBCDBADACBCEBAFG $.

  $( If a proposition is false, then implying it is equivalent to being false.
     One of four theorems that can be used to simplify an implication
     ` ( ph -> ps ) ` , the other ones being ~ ax-i1 (true consequent),
     ~ pm2.21 (false antecedent), ~ pm5.5 (true antecedent).  (Contributed by
     Mario Carneiro, 26-Apr-2019.)  (Proof shortened by Wolf Lammen,
     26-May-2019.) $)
  imnot $p |- ( -. ps -> ( ( ph -> ps ) <-> -. ph ) ) $=
    ( wn wi mtt bicomd ) BCACABDBAEF $.

  $( Theorem *5.501 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    ( wb pm5.1im biimp com12 impbid ) ABABCABDABCABABEFG $.

  $( The negation of a wff is equivalent to the wff's equivalence to falsehood.
     (Contributed by Juha Arpiainen, 19-Jan-2006.)  (Proof shortened by Wolf
     Lammen, 28-Jan-2013.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.501 notbi bitr4di ) ACBCACBCDABDACBCEABFG $.

  $( Transfer negation via an equivalence.  (Contributed by NM, 3-Oct-2007.)
     (Proof shortened by Wolf Lammen, 28-Jan-2013.) $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    ( wn wb nbn2 bicom bitr2di ) BCACBADABDBAEBAFG $.

  ${
    nbn.1 $e |- -. ph $.
    $( The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (Contributed by NM, 21-Jun-1993.)  (Proof shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $=
      ( wb wn bibif ax-mp bicomi ) BADBEAEBADBEDCBAFGH $.
  $}

  ${
    nbn3.1 $e |- ph $.
    $( Transfer falsehood via equivalence.  (Contributed by NM,
       11-Sep-2006.) $)
    nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $=
      ( wn notnoti nbn ) ADBACEF $.
  $}

  $( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ biimpr -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.) $)
  pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $=
    ( wn wb nbn2 biimpd ) ACBCABDABEF $.

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent.  (Contributed by NM, 4-Apr-2005.)  (Proof
       shortened by Wolf Lammen, 19-May-2013.) $)
    2false $p |- ( ph <-> ps ) $=
      ( wn 2th con4bii ) ABAEBECDFG $.
  $}

  ${
    2falsed.1 $e |- ( ph -> -. ps ) $.
    2falsed.2 $e |- ( ph -> -. ch ) $.
    $( Two falsehoods are equivalent (deduction form).  (Contributed by NM,
       11-Oct-2013.)  (Proof shortened by Wolf Lammen, 11-Apr-2024.) $)
    2falsed $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wn 2thd con4bid ) ABCABFCFDEGH $.
  $}

  ${
    pm5.21ni.1 $e |- ( ph -> ps ) $.
    pm5.21ni.2 $e |- ( ch -> ps ) $.
    $( Two propositions implying a false one are equivalent.  (Contributed by
       NM, 16-Feb-1996.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $=
      ( wn con3i 2falsed ) BFACABDGCBEGH $.
  $}


  $( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122.  (Contributed by NM, 11-May-1993.) $)
  bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $=
    ( wi ax-i3 impbii ) ABCDDBACDDABCEBACEF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical disjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section defines disjunction of two formulas, denoted by infix " ` \/ ` "
  and read "or".  It is defined in terms of implication and negation, which is
  possible in classical logic (but not in intuitionistic logic: see iset.mm).
  This section contains only theorems proved without {TODO} df-an (theorems
  that are
  proved using {TODO} df-an are deferred to the next section).
  Basic theorems that
  help simplifying and applying disjunction are ~ olc , ~ orc , and ~ orcom .

  As mentioned in the "note on definitions" in the section comment for logical
  equivalence, all theorems in this and the previous section can be stated in
  terms of implication and negation only.  Additionally, in classical logic
  (but not in intuitionistic logic: see iset.mm), it is also possible to
  translate conjunction into disjunction and conversely via the De Morgan law
  {TODO} anor : conjunction and disjunction are dual connectives.  Either is
  sufficient to develop all propositional calculus of the logic (together with
  implication and negation).  In practice, conjunction is more efficient, its
  big advantage being the possibility to use it to group antecedents in a
  convenient way, using {TODO} imp and {TODO} ex as noted in the previous
  section.

  An illustration of the conservativity of {TODO} df-an is given by
  {TODO} orim12dALT ,
  which is an alternate proof of {TODO} orim12d not using {TODO} df-an .

$)


  $( Declare connectives for disjunction ("or"). $)
  $c \/ $.  $( Vee (read:  "or") $)

  $( Extend wff definition to include disjunction ("or"). $)
  wo $a wff ( ph \/ ps ) $.

  $( Define disjunction (logical "or").  (Contributed by Lllllllllwith10ls,
     18-Jun-2026.) $)
  df-or $a |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $.


  $( Analog of theorem *4.64 of [WhiteheadRussell] p. 120.  (Contributed by
     Lllllllllwith10ls, 18-Jun-2026.) $)
  pm4.64 $p |- ( ( ( ph -> ps ) -> ps ) <-> ( ph \/ ps ) ) $=
    ( wo wi df-or bicomi ) ABCABDBDABEF $.

  $( Analog of theorem *4.66 of [WhiteheadRussell] p. 120.  (Contributed by
     Lllllllllwith10ls, 18-Jun-2026.) $)
  pm4.66 $p |- ( ( ( ph -> -. ps ) -> -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn pm4.64 ) ABCD $.

  $( Analog of theorem *2.53 of [WhiteheadRussell] p. 107.  (Contributed by
     Lllllllllwith10ls, 18-Jun-2026.) $)
  pm2.53 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wo wi df-or biimpi ) ABCABDBDABEF $.

  $( Analog of theorem *2.54 of [WhiteheadRussell] p. 107.  (Contributed by
     Lllllllllwith10ls, 18-Jun-2026.) $)
  pm2.54 $p |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $=
    ( wo wi df-or biimpri ) ABCABDBDABEF $.

  ${
    jaoi.1 $e |- ( ph -> ps ) $.
    jaoi.2 $e |- ( ch -> ps ) $.
    $( Inference disjoining the antecedents of two implications.  (Contributed
       by Lllllllllwith10ls, 19-Jun-2026.) $)
    jaoi $p |- ( ( ph \/ ch ) -> ps ) $=
      ( wo wi pm2.53 ax-i4 imim1i pm2.54 3syl mpisyl ) ACFABFABGBACFACGCGCAGAGA
      BFACHACICAGAGBAGAGABGBGABFBAGCAGACBAEJJBAIABKLLDABHM $.
  $}

  ${
    jao1i.1 $e |- ( ps -> ( ch -> ph ) ) $.
    $( Add a disjunct in the antecedent of an implication.  (Contributed by
       Rodolfo Medina, 24-Sep-2010.) $)
    jao1i $p |- ( ( ph \/ ps ) -> ( ch -> ph ) ) $=
      ( wi ax-i1 jaoi ) ACAEBACFDG $.
  $}


  ${
    jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 18-Aug-1994.) $)
    jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $=
      ( wo wi com12 jaoi ) BDGACBACHDABCEIADCFIJI $.
  $}


  ${
    ori.1 $e |- ( ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by Lllllllllwith10ls,
       18-Jun-2026.) $)
    ori $p |- ( ( ph -> ps ) -> ps ) $=
      ( wo wi df-or mpbi ) ABDABEBECABFG $.
  $}

  ${
    orri.1 $e |- ( ( ph -> ps ) -> ps ) $.
    $( Infer disjunction from implication.  (Contributed by Lllllllllwith10ls,
       18-Jun-2026.) $)
    orri $p |- ( ph \/ ps ) $=
      ( wo wi df-or mpbir ) ABDABEBECABFG $.
  $}

  ${
    orrd.1 $e |- ( ph -> ( ( ps -> ch ) -> ch ) ) $.
    $( Deduce disjunction from implication.  (Contributed by Lllllllllwith10ls,
       18-Jun-2026.) $)
    orrd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wi wo pm2.54 syl ) ABCECEBCFDBCGH $.
  $}

  ${
    ord.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduce implication from disjunction.  (Contributed by Lllllllllwith10ls,
       18-Jun-2026.) $)
    ord $p |- ( ph -> ( ( ps -> ch ) -> ch ) ) $=
      ( wo wi df-or sylib ) ABCEBCFCFDBCGH $.
  $}


  ${
    orci.1 $e |- ph $.
    $( Deduction introducing a disjunct.  (Contributed by Lllllllllwith10ls,
       18-Jun-2026.) $)
    orci $p |- ( ph \/ ps ) $=
      ( wi a1i ax-i4 ax-mp orri ) ABBADADABDBDABADCEBAFGH $.

    $( Deduction introducing a disjunct.  (Contributed by Lllllllllwith10ls,
       18-Jun-2026.) $)
    olci $p |- ( ps \/ ph ) $=
      ( wi a1i orri ) BAABADCEF $.
  $}

  $( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104.

     (Contributed by Lllllllllwith10ls, 18-Jun-2026.) $)
  orc $p |- ( ph -> ( ph \/ ps ) ) $=
    ( pm2.27 orrd ) AABABCD $.

  $( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96.
     (Contributed by Lllllllllwith10ls, 18-Jun-2026.) $)
  olc $p |- ( ph -> ( ps \/ ph ) ) $=
    ( wi ax-i1 orrd ) ABAABACDE $.

  $( Axiom *1.4 of [WhiteheadRussell] p. 96.  (Contributed by
     Lllllllllwith10ls, 18-Jun-2026.) $)
  pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
    ( wi wo ax-i4 df-or 3imtr4i ) ABCBCBACACABDBADABEABFBAFG $.

  $( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 15-Nov-2012.) $)
  orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $=
    ( wo pm1.4 impbii ) ABCBACABDBADE $.


  ${
    orcomd.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Commutation of disjuncts in consequent.  (Contributed by NM,
       2-Dec-2010.) $)
    orcomd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( wo orcom sylib ) ABCECBEDBCFG $.
  $}

  ${
    orcoms.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Commutation of disjuncts in antecedent.  (Contributed by NM,
       2-Dec-2012.) $)
    orcoms $p |- ( ( ps \/ ph ) -> ch ) $=
      ( wo pm1.4 syl ) BAEABECBAFDG $.
  $}

  ${
    orcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IR ( ` \/ ` insertion right).  (Contributed by NM,
       20-Sep-2007.) $)
    orcd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wo orc syl ) ABBCEDBCFG $.

    $( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IL ( ` \/ ` insertion left).  (Contributed by NM,
       11-Apr-2008.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    olcd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( orcd orcomd ) ABCABCDEF $.
  $}

  ${
    orcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof.  (Contributed by NM, 21-Jun-1994.) $)
    orcs $p |- ( ph -> ch ) $=
      ( wo orc syl ) AABECABFDG $.
  $}

  ${
    olcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct.  (Contributed by NM, 21-Jun-1994.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    olcs $p |- ( ps -> ch ) $=
      ( orcoms orcs ) BACABCDEF $.
  $}

  ${
    pm3.2ni.1 $e |- -. ph $.
    pm3.2ni.2 $e |- -. ps $.
    $( Infer negated disjunction of negated premises.  (Contributed by
       Lllllllllwith10ls, 18-Jun-2026.) $)
    pm3.2ni $p |- -. ( ph \/ ps ) $=
      ( wo wi wn pm2.53 pm2.21 ax-i4 syl5 mpisyl mto ) ABEACABEABFBFBGAABHDBGBA
      FABFBFABAIABJKLM $.
  $}

  $( Theorem *2.45 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.45 $p |- ( -. ( ph \/ ps ) -> -. ph ) $=
    ( wo orc con3i ) AABCABDE $.

  $( Theorem *2.46 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.46 $p |- ( -. ( ph \/ ps ) -> -. ps ) $=
    ( wo olc con3i ) BABCBADE $.

  $( Theorem *2.47 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.47 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $=
    ( wo wn pm2.45 orcd ) ABCDADBABEF $.

  $( Theorem *2.48 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.48 $p |- ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDAABEF $.

  $( Theorem *2.49 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.49 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDADABEF $.

  $( If neither of two propositions is true, then these propositions are
     equivalent.  (Contributed by BJ, 26-Apr-2019.) $)
  norbi $p |- ( -. ( ph \/ ps ) -> ( ph <-> ps ) ) $=
    ( wo orc olc pm5.21ni ) AABCBABDBAEF $.

  $( If two propositions are not equivalent, then at least one is true.
     (Contributed by BJ, 19-Apr-2019.)  (Proof shortened by Wolf Lammen,
     19-Jan-2020.) $)
  nbior $p |- ( -. ( ph <-> ps ) -> ( ph \/ ps ) ) $=
    ( wo wb norbi con1i ) ABCABDABEF $.

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (Contributed by Lllllllllwith10ls,
     18-Jun-2026.) $)
  orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wi wn wo jarl pm2.53 syl11 ) ABCBCADBABEABBFABGH $.

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (Contributed by Lllllllllwith10ls,
     18-Jun-2026.) $)
  orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $=
    ( wo wi wn pm2.53 pm2.21 ax-i4 syl2imc ) BACBADADAEABDBBAFABGBAHI $.

  $( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.) $)
  pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $=
    ( wo orc imim1i ) AACDBACEF $.

  $( Theorem *2.67 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $=
    ( pm2.67-2 ) ABBC $.


  $( Theorem *2.621 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wi id idd jaod ) ABCABBABCDABCBEF $.

  $( Theorem *2.07 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.07 $p |- ( ph -> ( ph \/ ph ) ) $=
    ( olc ) AAB $.

  $( Axiom *1.2 of [WhiteheadRussell] p. 96, which they call "Taut".
     (Contributed by NM, 3-Jan-2005.) $)
  pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $=
    ( wo wi id pm2.53 mpi ) AABAACAADAAEF $.

  $( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (Contributed by Lllllllllwith10ls, 18-Jun-2026.) $)
  oridm $p |- ( ( ph \/ ph ) <-> ph ) $=
    ( wo pm1.2 pm2.07 impbii ) AABAACADE $.

  $( Theorem *4.25 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.25 $p |- ( ph <-> ( ph \/ ph ) ) $=
    ( wo oridm bicomi ) AABAACD $.

  $( Theorem *2.4 of [WhiteheadRussell] p. 106.  (Contributed by
     Lllllllllwith10ls, 18-Jun-2026.) $)
  pm2.4 $p |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo wi orc pm2.53 mpi ) AABCCAABCDABCABEAABCFG $.

  $( Theorem *2.41 of [WhiteheadRussell] p. 106.  (Contributed by
     Lllllllllwith10ls, 18-Jun-2026.) $)
  pm2.41 $p |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo wi olc pm2.53 mpi ) BABCCBABCDABCBAEBABCFG $.

  ${
    orim12i.1 $e |- ( ph -> ps ) $.
    orim12i.2 $e |- ( ch -> th ) $.
    $( Disjoin antecedents and consequents of two premises.  (Contributed by
       Lllllllllwith10ls, 18-Jun-2026.) $)
    orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $=
      ( wo orcd olcd jaoi ) ABDGCABDEHCDBFIJ $.
  $}

  ${
    orim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $=
      ( id orim12i ) ABCCDCEF $.

    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $=
      ( id orim12i ) CCABCEDF $.
  $}

  ${
    orbi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a left disjunct to both sides of a logical equivalence.
       (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen,
       12-Dec-2012.) $)
    orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $=
      ( wo biimpi orim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.

    $( Inference adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 3-Jan-1993.) $)
    orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $=
      ( wo orcom orbi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
  $}

  ${
    orbi12i.1 $e |- ( ph <-> ps ) $.
    orbi12i.2 $e |- ( ch <-> th ) $.
    $( Infer the disjunction of two equivalences.  (Contributed by NM,
       3-Jan-1993.) $)
    orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $=
      ( wo orbi2i orbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
  $}


  $( Theorem *4.37 of [WhiteheadRussell] p. 118.  (Contributed by
     Lllllllllwith10ls, 19-Jun-2026.) $)
  orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $=
    ( wb wo biimp orc syl6 wi olc a1i jaod biimpr impbid ) ABDACEBCEABDABCECABD
    ABBCEABFBCGHCBCEIABDCBJKLABDBACECABDBAACEABMACGHCACEIABDCAJKLN $.

  $( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
  pm1.5 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo orc olcd olc orim2i jaoi ) ABACDDBCDAACDBACEFCACDBCAGHI $.

  $( Swap two disjuncts.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 14-Nov-2012.) $)
  or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo pm1.5 impbii ) ABCDDBACDDABCEBACEF $.

  $( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
  orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orcom or12 orbi2i 3bitri ) ABDCDCABDDACBDDABCDDABDCECABFCBDBCDACBEGH
    $.

  $( Theorem *2.31 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.31 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $=
    ( wo orass biimpri ) ABDCDABCDDABCEF $.

  $( Theorem *2.32 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.32 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orass biimpi ) ABDCDABCDDABCEF $.

  $( Theorem *2.3 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.3 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $=
    ( wo pm1.4 orim2i ) BCDCBDABCEF $.


  $( A rearrangement of disjuncts.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)
  or32 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $=
    ( wo orass or12 orcom 3bitri ) ABDCDABCDDBACDDACDBDABCEABCFBACDGH $.

  $( Rearrangement of 4 disjuncts.  (Contributed by NM, 12-Aug-1994.) $)
  or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $=
    ( wo or12 orbi2i orass 3bitr4i ) ABCDEEEACBDEEEABECDEEACEBDEEBCDEECBDEEABCD
    FGABCDEHACBDEHI $.

  $( Rearrangement of 4 disjuncts.  (Contributed by NM, 10-Jan-2005.) $)
  or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                 ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $=
    ( wo or4 orcom orbi2i bitri ) ABECDEEACEBDEEACEDBEEABCDFBDEDBEACEBDGHI $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
  orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <->
               ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    ( wo oridm orbi1i or4 bitr3i ) ABCDDAADBCDDABDACDDAADABCDAEFAABCGH $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
  orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <->
               ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $=
    ( wo oridm orbi2i or4 bitr3i ) ABDCDABDCCDDACDBCDDCCDCABDCEFABCCGH $.


  $( A disjunction with a true formula is equivalent to that true formula.
     (Contributed by NM, 23-May-1999.) $)
  biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $=
    ( wo id orc 2thd ) AAABCADABEF $.

  $( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 23-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 18-Nov-2012.) $)
  biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wn wo olc orel1 impbid2 ) ACBABDBAEABFG $.

  $( A wff is equivalent to its negated disjunction with falsehood.
     (Contributed by NM, 9-Jul-2012.) $)
  biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $=
    ( wn wo wb notnot biorf syl ) AACCBACBDEAFACBGH $.

  ${
    biorfi.1 $e |- -. ph $.
    $( The dual of ~ biorf is not {TODO} biantr but {TODO} iba (and {TODO}
       ibar ).  So there should also be a "biorfr".  (Note that these four
       statements can actually be strengthened to biconditionals.)
       (Contributed by BJ, 26-Oct-2019.) $)
    biorfi $p |- ( ps <-> ( ph \/ ps ) ) $=
      ( wn wo wb biorf ax-mp ) ADBABEFCABGH $.

    $( A wff is equivalent to its disjunction with falsehood.  (Contributed by
       NM, 23-Mar-1995.)  (Proof shortened by Wolf Lammen, 16-Jul-2021.)
       (Proof shortened by AV, 10-Aug-2025.) $)
    biorfri $p |- ( ps <-> ( ps \/ ph ) ) $=
      ( wo biorfi orcom bitri ) BABDBADABCEABFG $.
  $}

  $( Contradiction and disjunction. $)

  $( Theorem *2.64 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.64 $p |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $=
    ( wn wo orel2 jao1i com12 ) ABCDABDAABCABDBAEFG $.

  $( Theorem *2.42 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.42 $p |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wn wi pm2.21 id jaoi ) ACABDABDABEABDFG $.

$( Some expressions connecting implication and disjunction. $)

  $( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 30-Jan-2013.) $)
  pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wo wb olc pm2.621 impbid2 orc biimpr syl5 impbii ) ABCBABDEABCBABDBAFA
    BGHAABDBABDEBABIBABDJKL $.

  $( Simplify an implication between implications.  (Contributed by Paul
     Chapman, 17-Nov-2012.)  (Proof shortened by Wolf Lammen, 3-Apr-2013.) $)
  imimorb $p |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <->
                  ( ph -> ( ps \/ ch ) ) ) $=
    ( wi wo bi2.04 df-or imbi2i bitr4i ) BCDACDDABCDCDDABCEDBCDACFBCEBCDCDABCGH
    I $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Strong disjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section defines disjunction of two formulas, denoted by infix
  " ` (x) ` ".

$)


  $( Declare connectives for strong disjunction. $)
  $c (+) $.

  $( Extend wff definition to include strong disjunction. $)
  wso $a wff ( ph (+) ps ) $.

  $( Define strong disjunction (logical "or").  (Contributed by
     Lllllllllwith10ls, 25-Jun-2026.) $)
  df-sor $a |- ( ( ph (+) ps ) <-> ( -. ph -> ps ) ) $.


  $( Theorem *4.64 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.64s $p |- ( ( -. ph -> ps ) <-> ( ph (+) ps ) ) $=
    ( wso wn wi df-sor bicomi ) ABCADBEABFG $.

  $( Theorem *4.66 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.66s $p |- ( ( -. ph -> -. ps ) <-> ( ph (+) -. ps ) ) $=
    ( wn pm4.64s ) ABCD $.

  $( Theorem *2.53 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.53s $p |- ( ( ph (+) ps ) -> ( -. ph -> ps ) ) $=
    ( wso wn wi df-sor biimpi ) ABCADBEABFG $.

  $( Theorem *2.54 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.54s $p |- ( ( -. ph -> ps ) -> ( ph (+) ps ) ) $=
    ( wso wn wi df-sor biimpri ) ABCADBEABFG $.

  ${
    sori.1 $e |- ( ph (+) ps ) $.
    $( Infer implication from disjunction.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    sori $p |- ( -. ph -> ps ) $=
      ( wso wn wi pm2.53s ax-mp ) ABDAEBFCABGH $.
  $}

  ${
    sorri.1 $e |- ( -. ph -> ps ) $.
    $( Infer disjunction from implication.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    sorri $p |- ( ph (+) ps ) $=
      ( wn wi wso pm2.54s ax-mp ) ADBEABFCABGH $.
  $}

  ${
    sorrd.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduce disjunction from implication.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    sorrd $p |- ( ph -> ( ps (+) ch ) ) $=
      ( wn wi wso pm2.54s syl ) ABECFBCGDBCHI $.
  $}

  ${
    sord.1 $e |- ( ph -> ( ps (+) ch ) ) $.
    $( Deduce implication from disjunction.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    sord $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wso wn wi pm2.53s syl ) ABCEBFCGDBCHI $.
  $}


  ${
    sorci.1 $e |- ph $.
    $( Deduction introducing a disjunct.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    sorci $p |- ( ph (+) ps ) $=
      ( pm2.24i sorri ) ABABCDE $.

    $( Deduction introducing a disjunct.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    solci $p |- ( ps (+) ph ) $=
      ( wn a1i sorri ) BAABDCEF $.
  $}

  $( Introduction of a disjunct.  (Contributed by Lllllllllwith10ls,
     18-Jun-2026.) $)
  sorc $p |- ( ph -> ( ph (+) ps ) ) $=
    ( pm2.24 sorrd ) AABABCD $.

  $( Introduction of a disjunct.  (Contributed by Lllllllllwith10ls,
     18-Jun-2026.) $)
  solc $p |- ( ph -> ( ps (+) ph ) ) $=
    ( wn ax-i1 sorrd ) ABAABCDE $.


  $( Strengthen disjunction.  (Contributed by Lllllllllwith10ls,
     20-Jul-2026.) $)
  orso $p |- ( ( ph \/ ps ) -> ( ph (+) ps ) ) $=
    ( wo wi wso pm2.53 jarl sorrd syl ) ABCABDBDABEABFABDBDABABBGHI $.

  $( Strengthen disjunction.  (Contributed by Lllllllllwith10ls,
     20-Jul-2026.) $)
  imimsoro $p |- ( ( ( ph (+) ps ) -> ch ) -> ( ( ph \/ ps ) -> ch ) ) $=
    ( wo wso orso imim1i ) ABDABECABFG $.


  $( Axiom *1.4 of [WhiteheadRussell] p. 96.  (Contributed by
     Lllllllllwith10ls, 25-Jun-2026.) $)
  pm1.4s $p |- ( ( ph (+) ps ) -> ( ps (+) ph ) ) $=
    ( wso pm2.53s con1d sorrd ) ABCBAABCABABDEF $.

  $( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 3-Jan-1993.) $)
  sorcom $p |- ( ( ph (+) ps ) <-> ( ps (+) ph ) ) $=
    ( wso pm1.4s impbii ) ABCBACABDBADE $.


  ${
    sorcomd.1 $e |- ( ph -> ( ps (+) ch ) ) $.
    $( Commutation of disjuncts in consequent.  (Contributed by NM,
       2-Dec-2010.) $)
    sorcomd $p |- ( ph -> ( ch (+) ps ) ) $=
      ( wso sorcom sylib ) ABCECBEDBCFG $.
  $}

  ${
    sorcoms.1 $e |- ( ( ph (+) ps ) -> ch ) $.
    $( Commutation of disjuncts in antecedent.  (Contributed by NM,
       2-Dec-2012.) $)
    sorcoms $p |- ( ( ps (+) ph ) -> ch ) $=
      ( wso pm1.4s syl ) BAEABECBAFDG $.
  $}


  ${
    sorcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    sorcd $p |- ( ph -> ( ps (+) ch ) ) $=
      ( wso sorc syl ) ABBCEDBCFG $.

    $( Deduction introducing a disjunct.  (Contributed by Lllllllllwith10ls,
       25-Jun-2026.) $)
    solcd $p |- ( ph -> ( ch (+) ps ) ) $=
      ( sorcd sorcomd ) ABCABCDEF $.
  $}

  ${
    sorcs.1 $e |- ( ( ph (+) ps ) -> ch ) $.
    $( Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof.  (Contributed by NM, 21-Jun-1994.) $)
    sorcs $p |- ( ph -> ch ) $=
      ( wso sorc syl ) AABECABFDG $.
  $}

  ${
    solcs.1 $e |- ( ( ph (+) ps ) -> ch ) $.
    $( Deduction eliminating disjunct.  (Contributed by NM, 21-Jun-1994.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    solcs $p |- ( ps -> ch ) $=
      ( sorcoms sorcs ) BACABCDEF $.
  $}

  ${
    pm3.2sni.1 $e |- -. ph $.
    pm3.2sni.2 $e |- -. ps $.
    $( Infer negated disjunction of negated premises.  (Contributed by
       Lllllllllwith10ls, 25-Jun-2026.) $)
    pm3.2sni $p |- -. ( ph (+) ps ) $=
      ( wso wn wi a1i ax-i4 ax-mp mto pm2.53s ) ABEAFBGAFBGBDBAFGAFGAFBGBGAFBAF
      GCHBAFIJKABLK $.
  $}


  $( Theorem *2.45 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.45s $p |- ( -. ( ph (+) ps ) -> -. ph ) $=
    ( wso sorc con3i ) AABCABDE $.

  $( Theorem *2.46 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.46s $p |- ( -. ( ph (+) ps ) -> -. ps ) $=
    ( wso solc con3i ) BABCBADE $.

  $( Theorem *2.47 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.47s $p |- ( -. ( ph (+) ps ) -> ( -. ph (+) ps ) ) $=
    ( wso wn pm2.45s sorcd ) ABCDADBABEF $.

  $( Theorem *2.48 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.48s $p |- ( -. ( ph (+) ps ) -> ( ph (+) -. ps ) ) $=
    ( wso wn pm2.46s solcd ) ABCDBDAABEF $.

  $( Theorem *2.49 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.49s $p |- ( -. ( ph (+) ps ) -> ( -. ph (+) -. ps ) ) $=
    ( wso wn pm2.46s solcd ) ABCDBDADABEF $.

  $( If neither of two propositions is true, then these propositions are
     equivalent.  (Contributed by BJ, 26-Apr-2019.) $)
  nsorbi $p |- ( -. ( ph (+) ps ) -> ( ph <-> ps ) ) $=
    ( wso sorc solc pm5.21ni ) AABCBABDBAEF $.

  $( If two propositions are not equivalent, then at least one is true.
     (Contributed by BJ, 19-Apr-2019.)  (Proof shortened by Wolf Lammen,
     19-Jan-2020.) $)
  nbisor $p |- ( -. ( ph <-> ps ) -> ( ph (+) ps ) ) $=
    ( wso wb nsorbi con1i ) ABCABDABEF $.

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (Contributed by Lllllllllwith10ls,
     18-Jun-2026.) $)
  sorel1 $p |- ( -. ph -> ( ( ph (+) ps ) -> ps ) ) $=
    ( wso wn pm2.53s com12 ) ABCADBABEF $.

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (Contributed by Lllllllllwith10ls,
     18-Jun-2026.) $)
  sorel2 $p |- ( -. ph -> ( ( ps (+) ph ) -> ps ) ) $=
    ( wso wn pm2.53s pm1.4s syl11 ) ABCADBBACABEBAFG $.

  $( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.) $)
  pm2.67-2s $p |- ( ( ( ph (+) ch ) -> ps ) -> ( ph -> ps ) ) $=
    ( wso sorc imim1i ) AACDBACEF $.

  $( Theorem *2.67 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.67s $p |- ( ( ( ph (+) ps ) -> ps ) -> ( ph -> ps ) ) $=
    ( pm2.67-2s ) ABBC $.


  $( Theorem *2.07 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.07s $p |- ( ph -> ( ph (+) ph ) ) $=
    ( solc ) AAB $.

  $( Axiom *1.2 of [WhiteheadRussell] p. 96, which they call "Taut".
     (Contributed by Lllllllllwith10ls, 26-Jun-2026.) $)
  pm1.2s $p |- ( ( ( ph (+) ph ) (+) ph ) -> ( ph (+) ph ) ) $=
    ( wso wn wi pm2.53s con3i imim1i con1 wo id con2 mpi pm2.54 syl orri pm2.32
    ax-i5 pm1.4 mp2b ori pm1.5 pm2.4 ax-mp 3syl sorrd ) AABABAAAABABAABCADACADC
    ADACADAABAEACADCAABCAAABACADAAEFGACADCADACACADDACADACADAHACACADACACACADIIAC
    ACADIACACACADIACACACADIDAAADCDACACADIDACACADIAAADCDACACACADIAAADCDAADACAJAA
    ADKLGAAADCDACACADIACAAADCDIACADIACAAADCDACADIIAAADCDACACADIIACADACIAAADCDIA
    CADACAAADCDIIACAAADCDIACADIACADACIAAADCDACADACIAAADCDDACADACDACDAAADCDDAAAD
    CDACADACDACDACADACIAAADCDACADACMGACAAADCQNOACADACAAADCDPACADACAAADCDIRSACAA
    ADCDACADPACAAADCDACADUASTNOACACADUBUCTNUDUE $.

  $( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (Contributed by Lllllllllwith10ls, 26-Jun-2026.) $)
  soridm $p |- ( ( ( ph (+) ph ) (+) ph ) <-> ( ph (+) ph ) ) $=
    ( wso pm1.2s sorc impbii ) AABABAABACAABADE $.

  $( Theorem *4.25 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.25s $p |- ( ( ph (+) ph ) <-> ( ( ph (+) ph ) (+) ph ) ) $=
    ( wso soridm bicomi ) AABABAABACD $.

  ${
    sorim12i.1 $e |- ( ph -> ps ) $.
    sorim12i.2 $e |- ( ch -> th ) $.
    $( Disjoin antecedents and consequents of two premises.  (Contributed by
       Lllllllllwith10ls, 20-Jul-2026.) $)
    sorim12i $p |- ( ( ph (+) ch ) -> ( ps (+) th ) ) $=
      ( wso wn wi pm2.53s con3i imim12i sorrd syl ) ACGAHCIBDGACJAHCIBDBHAHCDAB
      EKFLMN $.
  $}


  ${
    sorim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    sorim2i $p |- ( ( ch (+) ph ) -> ( ch (+) ps ) ) $=
      ( id sorim12i ) CCABCEDF $.

    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    sorim1i $p |- ( ( ph (+) ch ) -> ( ps (+) ch ) ) $=
      ( id sorim12i ) ABCCDCEF $.
  $}

  ${
    sorbi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a left disjunct to both sides of a logical equivalence.
       (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen,
       12-Dec-2012.) $)
    sorbi2i $p |- ( ( ch (+) ph ) <-> ( ch (+) ps ) ) $=
      ( wso biimpi sorim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.

    $( Inference adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 3-Jan-1993.) $)
    sorbi1i $p |- ( ( ph (+) ch ) <-> ( ps (+) ch ) ) $=
      ( wso sorcom sorbi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
  $}

  ${
    sorbi12i.1 $e |- ( ph <-> ps ) $.
    sorbi12i.2 $e |- ( ch <-> th ) $.
    $( Infer the disjunction of two equivalences.  (Contributed by NM,
       3-Jan-1993.) $)
    sorbi12i $p |- ( ( ph (+) ch ) <-> ( ps (+) th ) ) $=
      ( wso sorbi2i sorbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
  $}


  $( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
  pm1.5s $p |- ( ( ph (+) ( ps (+) ch ) ) -> ( ps (+) ( ph (+) ch ) ) ) $=
    ( wso wn wi pm2.53s ax-i3 df-sor imbi2i 3imtr4i sorrd syl ) ABCDDAEBCDFBACD
    DABCDGAEBCDFBACDAEBECFFBEAECFFAEBCDFBEACDFAEBECHBCDBECFAEBCIJACDAECFBEACIJK
    LM $.

  $( Swap two disjuncts.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 14-Nov-2012.) $)
  sor12 $p |- ( ( ph (+) ( ps (+) ch ) ) <-> ( ps (+) ( ph (+) ch ) ) ) $=
    ( wso pm1.5s impbii ) ABCDDBACDDABCEBACEF $.

  $( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
  sorass $p |- ( ( ( ph (+) ps ) (+) ch ) <-> ( ph (+) ( ps (+) ch ) ) ) $=
    ( wso sorcom sor12 sorbi2i 3bitri ) ABDCDCABDDACBDDABCDDABDCECABFCBDBCDACBE
    GH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  "Modal" operators
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

$)

  $( Declare the possible operator. $)
  $c <> $.  $( Diamond (read:  "possibly") $)

  $( Extend wff definition to include the possible operator. $)
  wpos $a wff <> ph $.

  $( Define the possible operator (Contributed by Lllllllllwith10ls,
     31-May-2026.) $)
  df-pos $a |- ( <> ph <-> ( -. ph -> ph ) ) $.


  $( Declare the necessary operator. $)
  $c [] $.  $( Box (read:  "necessarily") $)

  $( Extend wff definition to include the necessary operator. $)
  wnec $a wff [] ph $.

  $( Define the necessary operator (Contributed by Lllllllllwith10ls,
     31-May-2026.) $)
  df-nec $a |- ( [] ph <-> -. <> -. ph ) $.


  $( Declare the doubtful operator. $)
  $c (.) $.  $( Wheel (read:  "doubtfully") $)

  $( Extend wff definition to include the doubtful operator. $)
  wdbt $a wff (.) ph $.

  $( Define the doubtful operator (Contributed by Lllllllllwith10ls,
     31-May-2026.) $)
  df-dbt $a |- ( (.) ph <-> ( ph <-> -. ph ) ) $.


  $( (Contributed by Lllllllllwith10ls, 31-May-2026.) $)
  mod-a1 $p |- ( ph -> <> ph ) $=
    ( wn wi wpos pm2.24 df-pos sylibr ) AABACADAAEAFG $.

  $( (Contributed by Lllllllllwith10ls, 31-May-2026.) $)
  mod-a2 $p |- ( [] ph -> ph ) $=
    ( wnec wn wpos df-nec mod-a1 con1i sylbi ) ABACDCAAEAACDACFGH $.


  $( (Contributed by Lllllllllwith10ls, 1-Jun-2026.) $)
  mod-a3 $p |- ( ph -> ( ph -> [] ph ) ) $=
    ( wn wpos wnec wi df-pos con4 sylbi com12 con2d df-nec imbitrrdi ) AAABCBAD
    AABCAABCAABABCABBABEAABEABFABAGHIJAKL $.

  $(
       (Contributed by Lllllllllwith10ls, 1-Jun-2026.)
    mod-a4 $p |- ( [] ( ph -> ps ) -> ( [] ph -> [] ps ) ) $=
      ( wn wpos wnec wi df-pos con4 sylbi com12 con2d df-nec imbitrrdi ) AAABZC
      ZBADANANAMNMBMEAMEMFMAGHIJAKL $. $)





















$( Begin $[ set-typeset.mm $] $)
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Appendix:  Typesetting definitions for the tokens in this file
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( $t

/* The '$ t' (no space between '$' and 't') token indicates the beginning
    of the typesetting definition section, embedded in a Metamath
    comment.  There may only be one per source file, and the typesetting
    section ends with the end of the Metamath comment.  The typesetting
    section uses C-style comment delimiters.  TODO:  Allow multiple
    typesetting comments */

/* These are the LaTeX and HTML definitions in the order the tokens are
    introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
    Metamath program. */

/* Note that the ALT= fields in htmldefs should be preceded by a space.  This
   ensures that a screen copy from the web page will have a space between
   symbols. */
/* Math font table with XITS and LaTeX defs:
   http://meeting.contextgarden.net/2011/talks/day3_05_ulrik_opentype/Samples/
           unimath-symbols.pdf */


/******* Web page format settings *******/

/* Custom CSS for Unicode fonts */
/* The woff font file was obtained from
   http://fred-wang.github.io/MathFonts/XITS/xits-math.woff 28-Aug-2015 */
htmlcss '<STYLE TYPE="text/css">\n' +
    '<!--\n' +
    '  .setvar { color: red; }\n' +
    '  .wff { color: blue; }\n' +
    '  .class { color: #C3C; }\n' +
    '  .symvar { border-bottom:1px dotted;color:#C3C}\n' +
    '  .typecode { color: gray }\n' +
    '  .hidden { color: gray }\n' +
    '  @font-face {\n' +
    '    font-family: XITSMath-Regular;\n' +
    '    src: url(xits-math.woff);\n' +
    '  }\n' +
    '  .math { font-family: XITSMath-Regular }\n' +
    '-->\n' +
    '</STYLE>\n' +
    '<LINK href="mmset.css" title="mmset"\n' +
    '    rel="stylesheet" type="text/css">\n' +
    '<LINK href="mmsetalt.css" title="mmsetalt"\n' +
    '    rel="alternate stylesheet" type="text/css">';

/* Tag(s) for the main SPAN surrounding all Unicode math */
htmlfont 'CLASS=math';

/* Page title, home page link */
htmltitle "Metamath Proof Explorer";
htmlhome '<A HREF="./index.html">Home</A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g., "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check existence of
   the references. */
htmlbibliography "mmset.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<SPAN CLASS=wff STYLE="color:blue;font-style:normal">wff</SPAN> '
    + '<SPAN CLASS=setvar STYLE="color:red;font-style:normal">setvar</SPAN> '
    + '<SPAN CLASS=class STYLE="color:#C3C;font-style:normal">class</SPAN>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
althtmldir ".\mpeuni\";


/******* Symbol definitions *******/

htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT=' (' TITLE='('>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=' )' TITLE=')'>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT=' -&gt;' TITLE='-&gt;'> ";
  althtmldef "->" as " &rarr; ";
  latexdef "->" as " \rightarrow ";
htmldef "-." as
    "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT=' -.' TITLE='-.'> ";
  althtmldef "-." as '&not; ';
  latexdef "-." as "\lnot";
htmldef "wff" as
    "<IMG SRC='_wff.gif' WIDTH=24 HEIGHT=19 ALT=' wff' TITLE='wff'> ";
  althtmldef "wff" as
    '<SPAN CLASS=typecode STYLE="color:gray">wff </SPAN>'; /* was #00CC00 */
  latexdef "wff" as "\mathrm{wff}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT=' |-' TITLE='|-'> ";
  althtmldef "|-" as
    '<SPAN CLASS=hidden STYLE="color:gray">&#8866; </SPAN>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|-" as "\vdash";
htmldef "&" as
    " <IMG SRC='amp.gif' WIDTH=12 HEIGHT=19 ALT='&amp;'> ";
  althtmldef "&" as " &amp; ";
  latexdef "&" as "\mathrel{\&}";
htmldef "=>" as
  " <IMG SRC='bigto.gif' WIDTH=15 HEIGHT=19 ALT='=&gt;'> ";
  althtmldef "=>" as " &rArr; ";
  latexdef "=>" as " \Rightarrow ";
htmldef "ph" as
    "<IMG SRC='_varphi.gif' WIDTH=11 HEIGHT=19 ALT=' ph' TITLE='ph'>";
  /* althtmldef "ph" as '<FONT COLOR="#0000FF">&#x1D711;</SPAN>'; */
  althtmldef "ph" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;</SPAN>';
  latexdef "ph" as "\varphi";
htmldef "ps" as "<IMG SRC='_psi.gif' WIDTH=12 HEIGHT=19 ALT=' ps' TITLE='ps'>";
  althtmldef "ps" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;</SPAN>';
  latexdef "ps" as "\psi";
htmldef "ch" as "<IMG SRC='_chi.gif' WIDTH=12 HEIGHT=19 ALT=' ch' TITLE='ch'>";
  althtmldef "ch" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;</SPAN>';
  latexdef "ch" as "\chi";
htmldef "th" as
    "<IMG SRC='_theta.gif' WIDTH=8 HEIGHT=19 ALT=' th' TITLE='th'>";
  althtmldef "th" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;</SPAN>';
  latexdef "th" as "\theta";
htmldef "ta" as "<IMG SRC='_tau.gif' WIDTH=10 HEIGHT=19 ALT=' ta' TITLE='ta'>";
  althtmldef "ta" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;</SPAN>';
  latexdef "ta" as "\tau";
htmldef "et" as "<IMG SRC='_eta.gif' WIDTH=9 HEIGHT=19 ALT=' et' TITLE='et'>";
  althtmldef "et" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;</SPAN>';
  latexdef "et" as "\eta";
htmldef "ze" as "<IMG SRC='_zeta.gif' WIDTH=9 HEIGHT=19 ALT=' ze' TITLE='ze'>";
  althtmldef "ze" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;</SPAN>';
  latexdef "ze" as "\zeta";
htmldef "si" as
    "<IMG SRC='_sigma.gif' WIDTH=10 HEIGHT=19 ALT=' si' TITLE='si'>";
  althtmldef "si" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;</SPAN>';
  latexdef "si" as "\sigma";
htmldef "rh" as "<IMG SRC='_rho.gif' WIDTH=9 HEIGHT=19 ALT=' rh' TITLE='rh'>";
  althtmldef "rh" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;</SPAN>';
  latexdef "rh" as "\rho";
htmldef "mu" as "<IMG SRC='_mu.gif' WIDTH=10 HEIGHT=19 ALT=' mu' TITLE='mu'>";
  althtmldef "mu" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D707;</SPAN>';
  latexdef "mu" as "\mu";
htmldef "la" as
    "<IMG SRC='_lambda.gif' WIDTH=9 HEIGHT=19 ALT=' la' TITLE='la'>";
  althtmldef "la" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D706;</SPAN>';
  latexdef "la" as "\lambda";
htmldef "ka" as
    "<IMG SRC='_kappa.gif' WIDTH=9 HEIGHT=19 ALT=' ka' TITLE='ka'>";
  althtmldef "ka" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D705;</SPAN>';
  latexdef "ka" as "\kappa";
htmldef "<->" as " <IMG SRC='leftrightarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' &lt;-&gt;' TITLE='&lt;-&gt;'> ";
  althtmldef "<->" as ' &harr; ';
  latexdef "<->" as "\leftrightarrow";
htmldef "<>" as " <IMG SRC='diamond.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' &lt;&gt;' TITLE='&lt;&gt;'> ";
  althtmldef "<>" as ' <span>&#9674;</span> ';
  latexdef "<>" as "\Diamond";
htmldef "[]" as " <IMG SRC='box.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' []' TITLE='[]'> ";
  althtmldef "[]" as ' <span>&#9633;</span> ';
  latexdef "[]" as "\Box";
htmldef "(.)" as " <IMG SRC='odot.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' (.)' TITLE='(.)'> ";
  althtmldef "(.)" as ' <span>&#10752;</span> ';
  latexdef "(.)" as "\odot";
htmldef "\/" as
     " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT=' \/' TITLE='\/'> ";
  althtmldef "\/" as ' &or; ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/" as "\vee";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT=' /\' TITLE='/\'> ";
  althtmldef "/\" as ' &and; ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "/\" as "\wedge";
htmldef "(+)" as
    " <IMG SRC='circleplus.gif' WIDTH=11 HEIGHT=19 ALT=' (+)' TITLE='(+)'> ";
  althtmldef "(+)" as ' <span>&#8853;</span> ';
  latexdef "(+)" as "\bigoplus";
htmldef "(x)" as
    " <IMG SRC='circletimes.gif' WIDTH=11 HEIGHT=19 ALT=' (x)' TITLE='(x)'> ";
  althtmldef "(x)" as ' <span>&#8855;</span> ';
  latexdef "(x)" as "\bigotimes";
htmldef "-/\" as
    " <IMG SRC='barwedge.gif' WIDTH=9 HEIGHT=19 ALT=' -/\' TITLE='-/\'> ";
  althtmldef "-/\" as ' &#8892; ';
    /*althtmldef "-/\" as " &#8892; "; */ /* too-high font bug in FF */
    /* barwedge, U022BC, alias ISOAMSB barwed, ['nand'] */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "-/\" as "\barwedge";
htmldef "\/_" as
    " <IMG SRC='veebar.gif' WIDTH=9 HEIGHT=19 ALT=' \/_' TITLE='\/_'> ";
  althtmldef "\/_" as " &#8891; ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/_" as "\mathrel{\underline{\vee}}";
htmldef "-\/" as
    " <IMG SRC='vee.gif' WIDTH=9 HEIGHT=19 ALT=' -\/' TITLE='-\/' " +
    " STYLE='text-decoration:overline;'> ";
  althtmldef "-\/" as
    ' <span>&#xFE0E;</span> ';
  latexdef "-\/" as "\mathrel{\overline{\vee}}";
  
htmldef "T." as
    " <IMG SRC='top.gif' WIDTH=11 HEIGHT=19 ALT='T.' TITLE='T.'> ";
  althtmldef "T." as '&#x22A4;';
  latexdef "T." as "\top";
/* End of typesetting definition section */
$)
$( End $[ set-typeset.mm $] $)

