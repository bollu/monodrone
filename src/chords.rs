// Theory of chords.
// We wish to be as good as https://www.scales-chords.com.
// Unfortunately, they have no docs, so we come up with an algorithm ourselves
// with cunning, guile and some rudimentary music theory.

// ### Music21
// Great library with deep theory to identify chord tones, but names them
//   completely nonsensically according to neo-riemannian theory.
//   Tables: https://github.com/cuthbertLab/music21/blob/e05fc53dfef7b2c9ac974c0cacb8b85e9c4d4605/music21/chord/tables.py
//   Algorithm: https://github.com/cuthbertLab/music21/blob/e05fc53dfef7b2c9ac974c0cacb8b85e9c4d4605/music21/analysis/reduceChords.py
// ### Musthe
// A python library that identifies chords, but doesn't have a lot of theory.
//   https://github.com/gciruelos/musthe/blob/9064aa3ae79880e00d92e05fe92515f807a4d925/musthe/musthe.py
// ### Textbook: Music theory for the 21st century
//   https://musictheory.pugetsound.edu/mt21c/ListsOfSetClasses.html
// ### Textbook: Open Music Theory
// - https://viva.pressbooks.pub/openmusictheory/chapter/set-class-and-prime-form/
// - https://viva.pressbooks.pub/openmusictheory/chapter/interval-class-vectors/
// #### Alan forte: The structure of atonal music
// - https://ianring.com/musictheory/scales/#primeform
// #### Wiki links:
// - Forte number: https://en.wikipedia.org/wiki/Forte_number
// - table: https://web.archive.org/web/20130118035710/http://solomonsmusic.net/pcsets.htm
//  prime form: "most compact" way of writing down a chord.
//  scale number: 12-bit number, of which tones are present.
//   interval vector:
//     perfect    | 5 semitones  |  P
//     Major 3rd  | 4 semitones  |  M
//     Minor 3rd  | 3 semitones  |  N
//     Second     | 2 semitones  |  S
//     Diminshed  | 1 semitones  |  D
//     Tritone    | 6 semitones  |  T

use core::fmt;
use std::{collections::{HashMap}};

use crate::datastructures::*;
use crate::constants::*;




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
    NoCommonName,
}

impl TriadQuality {
    pub fn str(&self) -> &str {
        match self {
            TriadQuality::Major => "M",
            TriadQuality::Minor => "m",
            TriadQuality::Diminished => "dim",
            TriadQuality::Augmented => "aug",
            TriadQuality::Suspended2 => "sus2",
            TriadQuality::Suspended4 => "sus4",
            TriadQuality::Dominant => "7",
            TriadQuality::MajorFlat5 => "M flat5",
            TriadQuality::NoCommonName => "NoName",
        }
    }
}

impl fmt::Display for TriadQuality {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
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
    NoCommonName, // it's a fourth chord, without a name.
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
            SeventhQuality::Major => "Major 7",
            SeventhQuality::Minor => "minor 7",
            SeventhQuality::Dominant => "7 / dom7",
            // ii7(flat 5) -> Vdom7 -> I
            SeventhQuality::HalfDiminished => "half diminished 7 / minor 7(♭5)",
            SeventhQuality::Diminished => "diminished 7",
            SeventhQuality::MinorMajor => "minor (major 7)",
            SeventhQuality::AugmentedMajor => "augmented Major 7",
            // end of table 1
            SeventhQuality::Augmented => "Augmented 7",
            SeventhQuality::DiminshedMajor => "Diminished Major 7 (flat 5)",
            SeventhQuality::DominantFlat5 => "Dominant 7 (flat 5)",
            SeventhQuality::MajorFlat5 => "Major (flat 5)",
            SeventhQuality::NoCommonName => "NoName"
        }
    }
}

impl fmt::Display for SeventhQuality {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

#[derive(Debug, PartialEq, Clone, Hash, Copy, Eq)]
pub enum TriadInversion {
    Root,
    First,
    Second,
}

impl TriadInversion {
    pub fn str(&self) -> &str {
        match self {
            TriadInversion::Root => "root",
            TriadInversion::First => "1st inversion",
            TriadInversion::Second => "2nd inversion",
        }
    }
}

impl fmt::Display for TriadInversion {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub struct Triad {
    pitches : Vec<Pitch>,
    quality : TriadQuality,
    inversion : TriadInversion
}

impl Triad {
    pub fn from_pitches(ps : Vec<Pitch>) -> Triad {

        let i12 = Interval::new(ps[0], ps[1]);
        let i23 = Interval::new(ps[1], ps[2]);
        let i13 = Interval::new(ps[0], ps[2]);
        println!("ps: {ps:?}, i12: {i12}, i23: {i23}");

        // C E G
        if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Minor3rd {
            Triad {
                pitches : ps,
                quality: TriadQuality::Major,
                inversion : TriadInversion::Root,

            }
        }
        // C Eb G
        else if i12.kind() == IntervalKind::Minor3rd && i23.kind() == IntervalKind::Major3rd {
            Triad {
                pitches : ps,
                quality: TriadQuality::Minor,
                inversion : TriadInversion::Root,
            }
        }
        // C E G#
        else if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Major3rd {
            Triad {
                pitches : ps,
                quality: TriadQuality::Augmented,
                inversion : TriadInversion::Root,
            }
        }
        // C E G#
        else if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Major3rd {
            Triad {
                pitches : ps,
                quality: TriadQuality::Augmented,
                inversion : TriadInversion::Root,
            }
        }
        // C Eb Gb
        else if i12.kind() == IntervalKind::Minor3rd && i23.kind() == IntervalKind::Minor3rd {
            Triad {
                pitches : ps,
                quality: TriadQuality::Diminished,
                inversion : TriadInversion::Root,
            }
        }

        // The term is borrowed from the contrapuntal technique of suspension,
        // where a note from a previous chord is carried over to the next chord,
        // and then resolved down to the third or tonic, suspending a note from
        // the previous chord.
        // C D G
        else if i12.kind() == IntervalKind::Major2nd && i13.kind() == IntervalKind::PerfectFifth {
            Triad {
                pitches : ps,
                quality: TriadQuality::Suspended2,
                inversion : TriadInversion::Root,
            }
        }
        // C F G
        else if i12.kind() == IntervalKind::PerfectFourth && i13.kind() == IntervalKind::PerfectFifth {
            Triad {
                pitches : ps,
                quality: TriadQuality::Suspended4,
                inversion : TriadInversion::Root,
            }
        }
        // C E Gb
        else if i12.kind() == IntervalKind::Major3rd && i23.kind() == IntervalKind::Major2nd {
            Triad {
                pitches : ps,
                quality: TriadQuality::MajorFlat5,
                inversion : TriadInversion::Root,
            }
        }
         else {
            Triad {
                pitches : ps,
                quality: TriadQuality::NoCommonName,
                inversion : TriadInversion::Root,
            }
        }
    }

    pub fn base(&self) -> Pitch {
        self.pitches[0]
    }


    pub fn string(&self) -> String {
        match self.quality {
            TriadQuality::NoCommonName => {
                let i12 = self.pitches[1] - self.pitches[0];
                let i13 = self.pitches[2] - self.pitches[1];
                format!("{}-{}", i12, i13).to_string()
            },
            _ => {
                if self.inversion == TriadInversion::Root {
                    format!("{}{}", self.base().str_no_octave(), self.quality).to_string()
                } else {
                    format!("{}-{} ({})", self.base().str_no_octave(), self.quality, self.inversion).to_string()
                }
            }
        }
    }
}


impl fmt::Display for Triad {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.string())
    }
}

impl Triad {
    // identify the "best" name for a given chord.
    // TODO: also use the key signature when doing so.
    pub fn identify_with_inversions(ps : &Vec<Pitch>, k : &KeySignature) -> Triad {
        let mut t1 = Triad::from_pitches(ps.clone());
        let mut t2 = Triad::from_pitches(vec![ps[1], ps[2], ps[0].raise_octave()]);
        let mut t3 = Triad::from_pitches(vec![ps[2], ps[0].raise_octave(), ps[1].raise_octave()]);
        t1.inversion = TriadInversion::Root;
        t2.inversion = TriadInversion::First;
        t3.inversion = TriadInversion::Second;

        println!("Triad::identify {t1:?}");
        println!("Triad::identify {t2:?}");
        println!("Triad::identify {t3:?}");

        if t1.quality != TriadQuality::NoCommonName {
            return t1
        } else if t2.quality != TriadQuality::NoCommonName {
            return t2
        } else {
            return t3
        }
    }
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub struct Seventh {
    pitches : Vec<Pitch>,
    quality : SeventhQuality,
}

impl Seventh {
    pub fn from_pitches(ps_orig : Vec<Pitch>) -> Seventh {
        println!("Seventh::from_pitches {ps_orig:?}");
        assert!(ps_orig.len() == 4);
        let mut ps = ps_orig.clone();
        // grab the triad first, now from_pitches the seventh.
        let triad = Triad::from_pitches(ps[0..3].to_vec());
        let _seventh = ps[3];
        // https://en.wikipedia.org/wiki/Seventh_chord
        let p34 = Interval::new(ps[2], ps[3]);
        match (triad.quality, p34.kind()) {
            // triad: M, 7 : M3
            // C E G B | all notes from the major scale
            (TriadQuality::Major, IntervalKind::Major3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Major,
                }
            },
            // triad: m, 7 : m3
            // C Eb G Bb // notes from the minor scale!
            (TriadQuality::Minor, IntervalKind::Minor3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Minor,
                }
            },
            // triad: M, 7: m3
            // C E G Bb
            (TriadQuality::Major, IntervalKind::Minor3rd) => { // usual 7th chord that I play
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Dominant,
                }
            },
            // triad: dim, 7 : M3
            // C Eb Gb Bb
            (TriadQuality::Diminished, IntervalKind::Major3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::HalfDiminished,
                }
            },
            // triad: dim, 7 : m3
            // C Eb Gb Bbb | confusing! we need the Gb to create enough space for Bbb.
            // stack of minor 3rd.
            (TriadQuality::Diminished, IntervalKind::Minor3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Diminished,
                }
            },
            // triad: m, 7 : M3
            // C Eb G B
            (TriadQuality::Minor, IntervalKind::Major3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::MinorMajor, // mysterious sound.
                }
            },
            // triad: aug/+, 7 : M3
            // C E G# B
            (TriadQuality::Augmented, IntervalKind::Major3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::AugmentedMajor,
                }

            }

            // --- end of table 1 ---
            // C E G# Bb
            (TriadQuality::Augmented, IntervalKind::Major2nd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Augmented,
                }
            },

            // triad: dim, 7 : augmented / perfect 4th
            // C Eb Gb B
            (TriadQuality::Diminished, IntervalKind::PerfectFourth) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::DiminshedMajor,
                }
            }
            // Dominant 7th flat 5
            // C E Gb Bb
            (TriadQuality::MajorFlat5, IntervalKind::Major3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::DominantFlat5,
                }
            },
            // major 7th flat 5
            // C E Gb B
            (TriadQuality::MajorFlat5, IntervalKind::Minor3rd) => {
                Seventh {
                    pitches : ps,
                    quality: SeventhQuality::Major,
                }
            },
            _ => {
                Seventh {
                    pitches : ps_orig,
                    quality: SeventhQuality::NoCommonName,
                }
            }
        }
    }


    fn base(&self) -> Pitch {
        self.pitches[0]
    }

    pub fn string(&self) -> String {
        match self.quality {
            SeventhQuality::NoCommonName => {
                let i12 = self.pitches[1] - self.pitches[0];
                let i13 = self.pitches[2] - self.pitches[1];
                let i14 = self.pitches[3] - self.pitches[2];
                format!("{}-{}-{}", i12, i13, i14).to_string()
            },
            _ => {
                format!("{}{}", self.base().str_no_octave(), self.quality).to_string()
            }
        }
    }
}

impl fmt::Display for Seventh {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.string())
    }
}

// Created to simulate https://www.scales-chords.com/chord/piano/D%237.
#[derive(Debug, PartialEq, Clone, Hash)]
pub struct TriadSkipForSeventh {
    orig_pitches : Vec<Pitch>,
    filler : Pitch, // pitch we fill in for the third.
    filling_index : usize,
    seventh : Seventh, // seventh chord we fake.
}

impl TriadSkipForSeventh {
    fn from_pitches(ps_orig : Vec<Pitch>, filling_index : usize, filler_pitch : Pitch) -> TriadSkipForSeventh {
        assert!(ps_orig.len() == 3);
        let mut ps = Vec::new();
        assert!(filling_index < 3);
        ps.extend(ps_orig[0..filling_index].to_vec());
        ps.push(filler_pitch);
        ps.extend(ps_orig[filling_index..3].to_vec());
        let seventh = Seventh::from_pitches(ps);

        TriadSkipForSeventh {
            orig_pitches : ps_orig,
            filler : filler_pitch,
            filling_index : filling_index,
            seventh : seventh,
        }
    }


    fn identify_no_inversion(ps : &Vec<Pitch>, k : &KeySignature) -> Vec<TriadSkipForSeventh> {
        // try all possibilities where we succeed in giving the damn thing a name.
        // TODO: use key signature.
        println!("--> identifying {ps:?}");
        assert!(ps.len() == 3);
        let mut out = Vec::new();
        for i in 0..3 {
            let p1 = ps[i];
            for pdelta in 0..12 {
                let filler = Pitch::from_pitch(p1.pitch() + pdelta);
                println!("------> filling index {i} with {filler}");
                let seventh = TriadSkipForSeventh::from_pitches(ps.clone(), i, filler);
                if seventh.seventh.quality != SeventhQuality::NoCommonName {
                    out.push(seventh);
                }
            }

        }
        out
    }

    fn identify_with_inversions(ps : &Vec<Pitch>, k : &KeySignature) -> Vec<TriadSkipForSeventh> {
        let mut out = Vec::new();
        println!("@@@@@ identifying {ps:?} with no inversion");
        out.extend(TriadSkipForSeventh::identify_no_inversion(&vec!(ps[0], ps[1], ps[2]), k));
        println!("@@@@@ identifying {ps:?} with 1st inversion");
        out.extend(TriadSkipForSeventh::identify_no_inversion(&vec!(ps[1], ps[2], ps[0].raise_octave()), k));
        println!("@@@@@ identifying {ps:?} with 2nd inversion");
        out.extend(TriadSkipForSeventh::identify_no_inversion(&vec!(ps[2], ps[0].raise_octave(), ps[1].raise_octave()), k));
        return out
    }

    pub fn string(&self) -> String {
        // TODO: implement the skipping printing.
        let ix : usize = self.filling_index.into();
        let mut out = String::new();

        out += &format!("{}{}", self.seventh.base().str_no_octave(), self.seventh.quality).to_string();
        out += "[";
        for i in 0..ix {
            out += &format!("{} ", self.orig_pitches[i].str_no_octave()).to_string();
        }
        out += &format!("(skip {}) ", self.filler.str_no_octave()).to_string();
        for i in ix..3 {
            out += &format!("{} ", self.orig_pitches[i].str_no_octave()).to_string();
        }
        out += "]";
        out

    }
}


#[derive(Debug, PartialEq, Clone, Hash)]
pub enum NoteGroup {
    Single (Pitch),
    Two(Interval),
    Three(Triad),
    ThreeFromSeventh(TriadSkipForSeventh),
    Four(Seventh),

    Unknown,
    None,
}

impl NoteGroup {
    pub fn identify(ps : Vec<Pitch>, k : KeySignature) -> NoteGroup {
        if ps.is_empty() {
            NoteGroup::None
        } else if ps.len() == 1 {
            NoteGroup::Single(ps[0])
        } else if ps.len() == 2 {
            NoteGroup::Two(Interval::new(ps[0], ps[1]))
        } else if ps.len() == 3 {
            let real_triad = Triad::identify_with_inversions(&ps, &k);
            if real_triad.quality != TriadQuality::NoCommonName {
                NoteGroup::Three(real_triad)
            } else {
                let fake_triads = TriadSkipForSeventh::identify_with_inversions(&ps, &k);
                if fake_triads.is_empty() {
                    NoteGroup::Unknown
                } else {
                    // TODO: order these chords.
                    NoteGroup::ThreeFromSeventh(fake_triads[0].clone())
                }
            }
        } else if ps.len() == 4 {
            NoteGroup::Four(Seventh::from_pitches(ps))
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
    pub fn rebuild(&mut self, track : &PlayerTrack, k : KeySignature) {
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
            self.note_groups.insert(y, NoteGroup::identify(ps, k));
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
