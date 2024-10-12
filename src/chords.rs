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
use crate::constants::*;



#[derive(Debug, PartialEq, PartialOrd, Clone, Eq, Hash, Ord, Copy)]
pub enum IntervalKind {
    PerfectOctave,
    Minor2nd,
    Major2nd, // diminished
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
            IntervalKind::Major2nd => "△2",
            IntervalKind::Minor3rd => "m3",
            IntervalKind::Major3rd => "△3",
            IntervalKind::PerfectFourth => "P4",
            IntervalKind::Tritone => "tritone",
            IntervalKind::PerfectFifth => "P5",
            IntervalKind::MinorSixth => "m6",
            IntervalKind::MajorSixth => "△6",
            IntervalKind::MinorSeventh => "m7",
            IntervalKind::MajorSeventh => "M7",
        }
    }

    pub fn diminish(&self) -> IntervalKind {
        match self {
            IntervalKind::PerfectOctave => IntervalKind::MajorSeventh,
            IntervalKind::Minor2nd => IntervalKind::PerfectOctave,
            IntervalKind::Major2nd => IntervalKind::Minor2nd,
            IntervalKind::Minor3rd => IntervalKind::Major2nd,
            IntervalKind::Major3rd => IntervalKind::Minor3rd,
            IntervalKind::PerfectFourth => IntervalKind::Major3rd,
            IntervalKind::Tritone => IntervalKind::PerfectFourth,
            IntervalKind::PerfectFifth => IntervalKind::Tritone,
            IntervalKind::MinorSixth => IntervalKind::PerfectFifth,
            IntervalKind::MajorSixth => IntervalKind::MinorSixth,
            IntervalKind::MinorSeventh => IntervalKind::MajorSixth,
            IntervalKind::MajorSeventh => IntervalKind::MinorSeventh,
        }
    }
    pub fn augment(&self) -> IntervalKind {
        match self {
            IntervalKind::PerfectOctave => IntervalKind::Minor2nd,
            IntervalKind::Minor2nd => IntervalKind::Major2nd,
            IntervalKind::Major2nd => IntervalKind::Minor3rd,
            IntervalKind::Minor3rd => IntervalKind::Major3rd,
            IntervalKind::Major3rd => IntervalKind::PerfectFourth,
            IntervalKind::PerfectFourth => IntervalKind::Tritone,
            IntervalKind::Tritone => IntervalKind::PerfectFifth,
            IntervalKind::PerfectFifth => IntervalKind::MinorSixth,
            IntervalKind::MinorSixth => IntervalKind::MajorSixth,
            IntervalKind::MajorSixth => IntervalKind::MinorSeventh,
            IntervalKind::MinorSeventh => IntervalKind::MajorSeventh,
            IntervalKind::MajorSeventh => IntervalKind::PerfectOctave,
        }
    }

    pub fn third() -> IntervalKind {
        IntervalKind::Major3rd
    }

    pub fn diminished_third() -> IntervalKind {
        IntervalKind::Minor3rd
    }

    pub fn augmented_third() -> IntervalKind {
        IntervalKind::PerfectFourth
    }

    pub fn fifth() -> IntervalKind {
        IntervalKind::PerfectFifth
    }

    pub fn diminished_fifth() -> IntervalKind {
        IntervalKind::Tritone
    }

    pub fn augmented_fifth() -> IntervalKind {
        IntervalKind::MinorSixth
    }

    pub fn seventh() -> IntervalKind {
        IntervalKind::MajorSeventh
    }

    pub fn diminished_seventh() -> IntervalKind {
        IntervalKind::MinorSeventh
    }

    // doesn't make much sense to augment a 7th.
    pub fn augmented_seventh() -> IntervalKind {
        IntervalKind::PerfectOctave
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

#[derive(Debug, PartialEq, Clone, Hash, Copy)]
pub enum TriadQuality {
    Major,
    Minor,
    Diminished,
    Augmented,
    Suspended2,
    Suspended4,
    Dominant,
    MajorFlat5,
}

impl TriadQuality {
    pub fn str(&self) -> &str {
        match self {
            TriadQuality::Major => "M",
            TriadQuality::Minor => "m",
            TriadQuality::Diminished => "o",
            TriadQuality::Augmented => "+",
            TriadQuality::Suspended2 => "sus2",
            TriadQuality::Suspended4 => "sus4",
            TriadQuality::Dominant => "7",
            TriadQuality::MajorFlat5 => "M♭5",
        }
    }
}

impl fmt::Display for TriadQuality {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}


impl fmt::Display for Triad {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.base().str_no_octave(), self.quality)
    }
}

// this is called quality in music theory:
// https://en.wikipedia.org/wiki/Interval_(music)#Quality
#[derive(Debug, PartialEq, Clone, Hash, Copy)]
pub enum SeventhQuality {
    Major,
    Minor,
    Diminished,
    HalfDiminished,
    DiminshedMajor,
    Augmented,
    AugmentedMajor,
    MinorMajor,
    DominantFlat5,
    MajorFlat5,
    Dominant,
}

// Major is Δ
// Minor is m
// Diminished is o
// Augmented is +
// Half diminished is ø
// Major flat 5 is M♭5
impl SeventhQuality {
    pub fn str(&self) -> &str {
        match self {
            SeventhQuality::Major => "Δ7",
            SeventhQuality::Minor => "m7",
            SeventhQuality::Dominant => "7 / dom7",
            // ii7(flat 5) -> Vdom7 -> I
            SeventhQuality::HalfDiminished => "ø7 / m7(♭5)",
            SeventhQuality::Diminished => "o7",
            SeventhQuality::MinorMajor => "m(Δ7)",
            SeventhQuality::AugmentedMajor => "+Δ7 / dom7♯5 / 7#5",
            // end of table 1
            SeventhQuality::Augmented => "+7",
            SeventhQuality::DiminshedMajor => "-Δ7♭5",
            SeventhQuality::DominantFlat5 => "7♭5",
            SeventhQuality::MajorFlat5 => "M♭5",
        }
    }
}

impl fmt::Display for SeventhQuality {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub struct Triad {
    pitches : Vec<Pitch>,
    quality : TriadQuality,
}

impl Triad {
    pub fn identify(ps : Vec<Pitch>) -> Option<Triad> {
        assert!(ps.len() == 3);

        if !(ps[0].pitch() < ps[1].pitch() && ps[1].pitch() < ps[2].pitch()) {
            return None
        }

        let i12 = Interval::new(ps[0], ps[1]);
        let i23 = Interval::new(ps[1], ps[2]);
        let i13 = Interval::new(ps[0], ps[2]);

        // C E G
        if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Minor3rd {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::Major,

            })
        }
        // C Eb G
        else if i12.kind() == IntervalKind::Minor3rd && i23.kind() == IntervalKind::Major3rd {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::Minor,
            })
        }
        // C E G#
        else if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Major3rd {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::Augmented,
            })
        }
        // C E G#
        else if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Major3rd {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::Augmented,
            })
        }
        // C Eb Gb
        else if i12.kind() == IntervalKind::Minor3rd && i23.kind() == IntervalKind::Minor3rd {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::Diminished,
            })
        }
        // The term is borrowed from the contrapuntal technique of suspension,
        // where a note from a previous chord is carried over to the next chord,
        // and then resolved down to the third or tonic, suspending a note from
        // the previous chord.
        // C D G
        else if i12.kind() == IntervalKind::Major2nd && i13.kind() == IntervalKind::PerfectFifth {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::Suspended2,
            })
        }
        // C F G
        else if i12.kind() == IntervalKind::PerfectFourth && i13.kind() == IntervalKind::PerfectFifth {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::Suspended4,
            })
        }
        // C E Gb
        else if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Major2nd {
            Some(Triad {
                pitches : ps,
                quality: TriadQuality::MajorFlat5,
            })
        }
         else {
            None
        }
    }

    pub fn base(&self) -> Pitch {
        self.pitches[0]
    }

    pub fn string(&self) -> String {
        format!("{}{}", self.base().str_no_octave(), self.quality).to_string()
    }
}


#[derive(Debug, PartialEq, Clone, Hash)]
pub struct Seventh {
    pitches : Vec<Pitch>,
    quality : SeventhQuality,
}

impl Seventh {
    pub fn identify(ps : Vec<Pitch>) -> Option<Seventh> {
        assert!(ps.len() == 4);
        if !(ps[0].pitch() < ps[1].pitch() && ps[1].pitch() < ps[2].pitch() && ps[2].pitch() < ps[3].pitch()) {
            return None
        }

        // grab the triad first, now identify the seventh.
        let triad = Triad::identify(ps[0..3].to_vec())?;
        let seventh = ps[3];
        // https://en.wikipedia.org/wiki/Seventh_chord
        let p34 = Interval::new(ps[2], ps[3]);
        match (triad.quality, p34.kind()) {
            // triad: M, 7 : M3
            // C E G B | all notes from the major scale
            (TriadQuality::Major, IntervalKind::Major3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Major,
                })
            },
            // triad: m, 7 : m3
            // C Eb G Bb // notes from the minor scale!
            (TriadQuality::Minor, IntervalKind::Minor3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Minor,
                })
            },
            // triad: M, 7: m3
            // C E G Bb
            (TriadQuality::Major, IntervalKind::Minor3rd) => { // usual 7th chord that I play
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Dominant,
                })
            },
            // triad: dim, 7 : M3
            // C Eb Gb Bb
            (TriadQuality::Diminished, IntervalKind::Major3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::HalfDiminished,
                })
            },
            // triad: dim, 7 : m3
            // C Eb Gb Bbb | confusing! we need the Gb to create enough space for Bbb.
            // stack of minor 3rd.
            (TriadQuality::Diminished, IntervalKind::Minor3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Diminished,
                })
            },
            // triad: m, 7 : M3
            // C Eb G B
            (TriadQuality::Minor, IntervalKind::Major3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::MinorMajor, // mysterious sound.
                })
            },
            // triad: aug/+, 7 : M3
            // C E G# B
            (TriadQuality::Augmented, IntervalKind::Major3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::AugmentedMajor,
                })

            }

            // --- end of table 1 ---
            // C E G# Bb
            (TriadQuality::Augmented, IntervalKind::Major2nd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Augmented,
                })
            },

            // triad: dim, 7 : augmented / perfect 4th
            // C Eb Gb B
            (TriadQuality::Diminished, IntervalKind::PerfectFourth) => {
                Some (Seventh {
                    pitches : ps,
                    quality: SeventhQuality::DiminshedMajor,
                })
            }
            // Dominant 7th flat 5
            // C E Gb Bb
            (TriadQuality::MajorFlat5, IntervalKind::Major3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::DominantFlat5,
                })
            },
            // major 7th flat 5
            // C E Gb B
            (TriadQuality::MajorFlat5, IntervalKind::Minor3rd) => {
                Some(Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Major,
                })
            },
            _ => None
        }
    }


    fn base(&self) -> Pitch {
        self.pitches[0]
    }

    pub fn string(&self) -> String {
        format!("{}{}{}", self.base().name, self.base().accidental, self.quality).to_string()
    }
}

impl fmt::Display for Seventh {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.string())
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub enum NoteGroup {
    Single (Pitch),
    Two(Interval),
    Three(Triad),
    Four(Seventh),

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
        } else if ps.len() == 3 {
            match Triad::identify(ps) {
                Some(t) => NoteGroup::Three(t),
                None => NoteGroup::Unknown,
            }
        } else if ps.len() == 4 {
            match Seventh::identify(ps) {
                Some(c) => NoteGroup::Four(c),
                None => NoteGroup::Unknown,
            }
        } else {
            NoteGroup::Unknown
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
        if !self.last_modified.is_dirty() {
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
