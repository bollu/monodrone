// Theory of chords
// https://github.com/cuthbertLab/music21/blob/e05fc53dfef7b2c9ac974c0cacb8b85e9c4d4605/music21/analysis/reduceChords.py
// 5fc53dfef7b2c9ac974c0cacb8b85e9c4d4605/music21/chord/tables.py
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

use core::fmt;
use std::{collections::{HashMap, HashSet},  time::Duration};

use crate::datastructures::*;



#[derive(Debug, PartialEq, PartialOrd, Clone, Eq, Hash, Ord, Copy)]
pub enum IntervalKind {
    PerfectOctave,
    Minor2nd,
    Major2nd,
    Minor3rd,
    Major3rd,
    PerfectFourth,
    Tritone,
    PerfectFifth,
    MinorSixth,
    MajorSixth,
    MinorSeventh,
    MajorSeventh,
}

impl IntervalKind {
    pub fn str(&self) -> &str {
        match self {
            IntervalKind::PerfectOctave => "octave",
            IntervalKind::Minor2nd => "m2",
            IntervalKind::Major2nd => "M2",
            IntervalKind::Minor3rd => "m3",
            IntervalKind::Major3rd => "M3",
            IntervalKind::PerfectFourth => "P4",
            IntervalKind::Tritone => "tritone",
            IntervalKind::PerfectFifth => "P5",
            IntervalKind::MinorSixth => "m6",
            IntervalKind::MajorSixth => "M6",
            IntervalKind::MinorSeventh => "m7",
            IntervalKind::MajorSeventh => "M7",
        }
    }
}

impl fmt::Display for IntervalKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

// an interval is a pair of pitches.
#[derive(Debug, PartialEq, Clone, Hash, Eq, Copy)]
pub struct Interval {
    pitches : (Pitch, Pitch),
}

impl Interval {
    fn new (p: Pitch, q: Pitch) -> Interval {
        Interval { pitches: (p, q) }
    }

    fn kind(&self) -> IntervalKind {
        let p = self.pitches.0;
        let q = self.pitches.1;
        let diff = if p.pitch() > q.pitch() {
            p.pitch() - q.pitch()
        } else {
            q.pitch() - p.pitch()
        };
        match diff {
            0 => IntervalKind::PerfectOctave,
            1 => IntervalKind::Minor2nd,
            2 => IntervalKind::Major2nd,
            3 => IntervalKind::Minor3rd,
            4 => IntervalKind::Major3rd,
            5 => IntervalKind::PerfectFourth,
            6 => IntervalKind::Tritone,
            7 => IntervalKind::PerfectFifth,
            8 => IntervalKind::MinorSixth,
            9 => IntervalKind::MajorSixth,
            10 => IntervalKind::MinorSeventh,
            11 => IntervalKind::MajorSeventh,
            _ => unreachable!("diff is modulo 12, so can only have values 1..11")
        }
    }

    pub fn string(&self) -> String {
        self.kind().str().to_string()
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.string())
    }
}

// this is called quality in music theory:
// https://en.wikipedia.org/wiki/Interval_(music)#Quality
#[derive(Debug, PartialEq, Clone, Hash, Copy)]
pub enum ChordQuality {
    Major,
    Minor,
    Diminished,
    // HalfDiminished,
    Augmented,
    // Dominant,
    Suspended2,
    Suspended4,
}

impl ChordQuality {
    pub fn str(&self) -> &str {
        match self {
            ChordQuality::Major => "M",
            ChordQuality::Minor => "m",
            ChordQuality::Diminished => "o",
            // ChordQuality::HalfDiminished => "ø",
            ChordQuality::Augmented => "⁺",
            ChordQuality::Suspended2 => "sus2",
            ChordQuality::Suspended4 => "sus4",
            // ChordQuality::Dominant => "dom",
        }
    }
}

impl fmt::Display for ChordQuality {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

#[derive(Debug, PartialEq, Clone, Hash, Copy)]
pub enum ChordInversion {
    Zeroth,
    First,
    Second
}

impl ChordInversion {

    pub fn str(&self) -> &str {
        match self {
            ChordInversion::Zeroth => "0",
            ChordInversion::First => "inv₁",
            ChordInversion::Second => "inv₂"
        }
    }
}

#[derive(Debug, PartialEq, Clone, Hash, Copy)]
pub enum ChordExtension {
    Seventh,
    Ninth,
    Eleventh,
    Thirteenth,
    None,
}

impl ChordExtension {
    pub fn str(&self) -> &str {
        match self {
            ChordExtension::Seventh => "7",
            ChordExtension::Ninth => "9",
            ChordExtension::Eleventh => "11",
            ChordExtension::Thirteenth => "13",
            ChordExtension::None => ""
        }
    }
}

// bass note slash
pub struct ChordSlash (Option<Pitch>);

// a 'real' chord with three of more notes.
#[derive(Debug, PartialEq, Clone, Hash)]
pub struct Chord {
    pitches : Vec<Pitch>,
    baseix: usize, // and index into pitches.
    quality : ChordQuality,
    inversion : ChordInversion,
    extension : ChordExtension
}


impl Chord {
    pub fn identify(ps : Vec<Pitch>) -> Option<Chord> {
        assert!(ps.len() >= 3);
        if ps.len() != 3 {
            return None
        }

        if !(ps[0].pitch() < ps[1].pitch() && ps[1].pitch() < ps[2].pitch()) {
            return None
        }

        let i12 = Interval::new(ps[0], ps[1]);
        let i23 = Interval::new(ps[1], ps[2]);
        let i13 = Interval::new(ps[0], ps[2]);

        if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Minor3rd {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Major,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        }
        else if i12.kind() == IntervalKind::Minor3rd && i23.kind() == IntervalKind::Major3rd {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Minor,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        }
        else if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Major3rd {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Augmented,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        }
        else if i12.kind() == IntervalKind::Minor3rd && i23.kind() == IntervalKind::Minor3rd {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Diminished,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        }
        // The term is borrowed from the contrapuntal technique of suspension,
        // where a note from a previous chord is carried over to the next chord,
        // and then resolved down to the third or tonic, suspending a note from
        // the previous chord.
        else if i12.kind() == IntervalKind::Major2nd && i13.kind() == IntervalKind::PerfectFifth {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Suspended2,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        } else if i12.kind() == IntervalKind::PerfectFourth && i13.kind() == IntervalKind::PerfectFifth {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Suspended4,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        }
         else {
            None
        }
    }

    pub fn base(&self) -> Pitch {
        self.pitches[self.baseix]
    }

    pub fn string(&self) -> String {
        format!("{}{}{}", self.base().name, self.base().accidental, self.quality).to_string()
    }
}

impl fmt::Display for Chord {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.string())
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub enum NoteGroup {
    Single (Pitch),
    Two(Interval),
    More(Chord),
    Unknown,
    None,
}

impl NoteGroup {
    pub fn mk(ps : Vec<Pitch>) -> NoteGroup {
        if ps.len() == 0 {
            NoteGroup::None
        } else if ps.len() == 1 {
            NoteGroup::Single(ps[0])
        } else if ps.len() == 2 {
            NoteGroup::Two(Interval::new(ps[0], ps[1]))
        } else {
            match Chord::identify(ps) {
                Some(c) => NoteGroup::More(c),
                None => NoteGroup::Unknown,
            }
        }
    }
}

// This is synchronized with a PlayerTrack.
#[derive(Clone, Debug, PartialEq)]
pub struct ChordInfo {
    // map from y to notegroup for that y.
    note_groups : HashMap<u64, NoteGroup>,
    last_modified : LastModified,
}

impl ChordInfo {
    pub fn rebuild(&mut self, track : &PlayerTrack) {
        // sync changes.
        self.last_modified.union(&track.last_modified);

        // We're not dirty, so return.
        if !self.last_modified.dirty {
            return
        }

        // we are dirty!
        self.last_modified.clean();
        // nuke our note groups, and rebuild them.
        // reuse storage so we don't allocate.
        self.note_groups.clear();

        for y in 0..TRACK_LENGTH {
            let mut ps = Vec::new();
            for x in 0..NTRACKS {
                match track.get_note_from_coord(x, y) {
                    Some(p) => ps.push(p.pitch),
                    None => continue,
                };
            }
            self.note_groups.insert(y, NoteGroup::mk(ps));
        }
    }

    pub fn get(&self, y : u64) -> &NoteGroup {
        assert!(y < TRACK_LENGTH);
        self.note_groups.get(&y).unwrap_or(&NoteGroup::None)
    }
}

impl Default for ChordInfo {
    fn default() -> ChordInfo {

        ChordInfo {
            note_groups: HashMap::new(),
            last_modified: LastModified::new(),
        }
    }
}
