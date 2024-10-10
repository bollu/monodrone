// Theory of chords
// https://github.com/cuthbertLab/music21/blob/e05fc53dfef7b2c9ac974c0cacb8b85e9c4d4605/music21/analysis/reduceChords.py
// https://github.com/gciruelos/musthe/blob/9064aa3ae79880e00d92e05fe92515f807a4d925/musthe/musthe.py
//
// Lead sheet notation: https://www.reddit.com/r/musictheory/comments/1h8tol/comment/caryq0w/
//
// https://musictheory.pugetsound.edu/mt21c/ListsOfSetClasses.html
//
// https://viva.pressbooks.pub/openmusictheory/chapter/set-class-and-prime-form/
// https://viva.pressbooks.pub/openmusictheory/chapter/interval-class-vectors/
//
// Alan forte: The structure of atonal music
// https://ianring.com/musictheory/scales/#primeform
// Forte number: https://en.wikipedia.org/wiki/Forte_number
// table: https://web.archive.org/web/20130118035710/http://solomonsmusic.net/pcsets.htm
//   prime form: "most compact" way of writing down a chord.
//   scale number: 12-bit number, of which tones are present.
//
//   interval vector:
//     perfect    | 5 semitones  |  P
//     Major 3rd  | 4 semitones  |  M 
//     Minor 3rd  | 3 semitones  |  N
//     Second     | 2 semitones  |  S
//     Diminshed  | 1 semitones  |  D
//     Tritone    | 6 semitones  |  T

enum ChordType {
    Major,
    Minor,
    Diminished,
    Augmented,
}

type Pitch = (NoteName, Accidental);

impl Show for ChordType {
    fn show(&self) {
        match self {
            Major => "M",
            Minor => "m",
            Diminished => "°",
            Augmented => "⁺",
        }
    }
}

enum ChordInversion {
    Zeroth,
    First,
    Second
}

impl Show for Inversion {
    fn show(&self) {
        match Self {
            Zeroth => "0",
            First => "inv₁",
            Second => "inv₂"
        }
    }
}

enum ChordExtension {
    Seventh,
    Ninth,
    Eleventh,
    Thirteenth,
}

// bass note slash
struct ChordSlash (Option<(NoteName)>);
struct Chord {
    base: NoteName,
    typ : ChordType,
    inversion : ChordInversion,
    extension : Extension,
    slash : ChordSlash
}
