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
use std::{collections::HashSet,  time::Duration};

use crate::datastructures::*;



#[derive(Debug, PartialEq, PartialOrd, Clone, Eq, Hash, Ord, Copy)]
enum IntervalKind {
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
    pub fn show(&self) -> &str {
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
        let diff = (p.pitch() - q.pitch()) % 12;
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

}

// this is called quality in music theory:
// https://en.wikipedia.org/wiki/Interval_(music)#Quality
#[derive(Debug, PartialEq, Clone, Hash, Copy)]
enum ChordQuality {
    Major,
    Minor,
    Diminished,
    Augmented,
}

impl ChordQuality {
    fn str(&self) -> &str {
        match self {
            ChordQuality::Major => "M",
            ChordQuality::Minor => "m",
            ChordQuality::Diminished => "°",
            ChordQuality::Augmented => "⁺",
        }
    }
}

impl fmt::Display for ChordQuality {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

#[derive(Debug, PartialEq, Clone, Hash, Copy)]
enum ChordInversion {
    Zeroth,
    First,
    Second
}

impl ChordInversion {

    fn show(&self) -> &str {
        match self {
            ChordInversion::Zeroth => "0",
            ChordInversion::First => "inv₁",
            ChordInversion::Second => "inv₂"
        }
    }
}

#[derive(Debug, PartialEq, Clone, Hash, Copy)]
enum ChordExtension {
    Seventh,
    Ninth,
    Eleventh,
    Thirteenth,
    None,
}

impl ChordExtension {
    fn show(&self) -> &str {
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
    fn identify(ps : Vec<Pitch>) -> Option<Chord> {
        assert!(ps.len() >= 3);
        if ps.len() != 3 {
            return None
        }

        if !(ps[0].pitch() < ps[1].pitch() && ps[1].pitch() < ps[2].pitch()) {
            return None
        }

        let i1 = Interval::new(ps[0], ps[1]);
        let i2 = Interval::new(ps[1], ps[2]);

        if i1.kind() == IntervalKind::Major3rd && i2.kind() == IntervalKind::Minor3rd {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Major,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        } else if i1.kind() == IntervalKind::Minor3rd && i2.kind() == IntervalKind::Major3rd {
            Some(Chord {
                pitches : ps,
                baseix: 0,
                quality: ChordQuality::Minor,
                inversion: ChordInversion::Zeroth,
                extension: ChordExtension::None
            })
        } else {
            None
        }
    }

    fn base(&self) -> Pitch {
        self.pitches[self.baseix]
    }

    fn show(&self) -> String {
        format!("{}{}{}", self.base().name, self.base().accidental, self.quality).to_string()
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
enum NoteGroup {
    Single (Pitch),
    Two(Interval),
    More(Chord),
    None,
    Unknown,
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
    note_groups : Vec<NoteGroup>,
    last_modified : LastModified,
}

impl ChordInfo {
    pub fn rebuild(&mut self, track : &PlayerTrack) {
        // sync changes.
        self.last_modified.union(&track.last_modified);

        // We're not dirty, so return.
        if !self.last_modified.is_dirty_and_idle_for(Duration::from_millis(100)) {
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
                let p = match track.get_note_from_coord(x, y) {
                    Some(p) => ps.push(p.pitch),
                    None => continue,
                };
            }
            self.note_groups.push(NoteGroup::mk(ps));
        }
    }
}

impl Default for ChordInfo {
    fn default() -> ChordInfo {
        ChordInfo {
            note_groups: Vec::new(),
            last_modified: LastModified::new(),
        }
    }
}
