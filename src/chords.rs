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

use std::collections::{HashMap, BTreeSet};
use itertools::Itertools;
use crate::datastructures::*;
use crate::constants::*;


// New algorithm design
// https://www.scales-chords.com/chord-database/piano/
// 1. normalize pitches into pitch classes
// 3. expand decision tree for each vertex, build full tree.
//    If any tree has a match, then try to find a match based on the following criteria in descending order:
//       1. no inversion, matches order.
//       2. only inversion, matches order.
//       3. no inversion, matches set.
//       4. (not needed) inversion, matches set: If we can match the set with an inversion, then we can match without.
//
//  An interesting wrinkle is how we deal with skipped notes.
//  In the scales-chords interface, they let a user 'skip' a note.

// an interval vector, holding intervals for the third, fifth, and seventh.
// Does *not* take into account inversion, and assumes that root < third < fifth < seventh.
// futhermore, if we are missing a third or a fifth or a seventh, we simply skip that index.
// higher indexes are marked with a zero.
// This enables hashing to find interval vectors that contain any given set of notes.
// Morally, this is a dense encoding of a set of pitches.


#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
enum ChordThirdKind {
    Major,
    Minor,
    Sus2,
    Sus4,
    Skip
}

impl ChordThirdKind {
    fn to_interval(&self) -> Option<IntervalKind> {
        match self {
            ChordThirdKind::Major => Some(IntervalKind::Major3rd),
            ChordThirdKind::Minor => Some(IntervalKind::Minor3rd),
            ChordThirdKind::Sus2 => Some(IntervalKind::Major2nd),
            ChordThirdKind::Sus4 => Some(IntervalKind::PerfectFourth),
            ChordThirdKind::Skip => None
        }
    }
    fn enumerate() -> Vec<ChordThirdKind> {
        vec!(ChordThirdKind::Major, ChordThirdKind::Minor, ChordThirdKind::Sus2, ChordThirdKind::Sus4, ChordThirdKind::Skip)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
enum ChordFifthKind {
    Skip,
    Perfect,
    Diminished,
    Augmented
}

impl ChordFifthKind {
    fn to_interval(&self) -> Option<IntervalKind> {
        match self {
            ChordFifthKind::Skip => None,
            ChordFifthKind::Perfect => Some(IntervalKind::PerfectFifth),
            ChordFifthKind::Diminished => Some(IntervalKind::Tritone),
            ChordFifthKind::Augmented => Some(IntervalKind::MinorSixth),
        }
    }

    fn enumerate() -> Vec<ChordFifthKind> {
        vec!(ChordFifthKind::Perfect, ChordFifthKind::Diminished, ChordFifthKind::Augmented)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
enum ChordSeventhKind {
    Skip,
    Major,
    Minor,
    Sixth
}

impl ChordSeventhKind {
    fn to_interval(&self) -> Option<IntervalKind> {
        match self {
            ChordSeventhKind::Skip => None,
            ChordSeventhKind::Major => Some(IntervalKind::MajorSeventh),
            ChordSeventhKind::Minor => Some(IntervalKind::MinorSeventh),
            ChordSeventhKind::Sixth => Some(IntervalKind::MajorSixth),
        }
    }

    fn enumerate() -> Vec<ChordSeventhKind> {
        vec!(ChordSeventhKind::Skip, ChordSeventhKind::Major, ChordSeventhKind::Minor, ChordSeventhKind::Sixth)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
struct Permutation(Vec<usize>);

impl Permutation {
    // the symmetric group that this permutation belongs to.
    fn len(&self) -> usize {
        self.0.len()
    }
    fn apply<T : Clone>(&self, v : Vec<T>) -> Vec<T> {
        assert!(v.len() == self.0.len());
        let mut out = Vec::new();
        for i in 0..self.0.len() {
            out.push(v[self.0[i]].clone());
        }
        out
    }

    fn num_cycles(&self) -> usize {
        let mut visited = vec![false; self.0.len()];
        let mut out = 0;
        for i in 0..self.0.len() {
            if visited[i] {
                continue;
            }
            out += 1;
            let mut j = i;
            while !visited[j] {
                visited[j] = true;
                j = self.0[j];
            }
        }
        out
    }

    fn generate(n : usize) -> Vec<Permutation> {
        (0..n).permutations(n).map(|p| { Permutation(p) }).collect()
    }
}


#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Chord {
    third : ChordThirdKind,
    fifth : ChordFifthKind,
    seventh : ChordSeventhKind,
    permutation : Permutation // permutation applied to chord.
}

impl Chord {

    // materialize the chord at the root.
    fn materialize_at_root(self, root : PitchClass) -> Vec<i32> {
        let intervals = vec!(self.third.to_interval(),
            self.fifth.to_interval(),
            self.seventh.to_interval());
        let mut base : Vec<i32> = vec!(root.into_pitch(0).pitch() as i32);

        for interval in intervals.into_iter().flatten() {
            let pitch_class = root + interval;
            base.push(pitch_class.into_pitch(0).pitch() as i32);
        }
        assert!(self.permutation.len() == base.len());
        self.permutation.apply(base)
    }

    fn badness(&self) -> i32 {
        let mut out : i32 = 0;

        out = out * 10 + match self.seventh {
            ChordSeventhKind::Skip => 0,
            ChordSeventhKind::Major => 1,
            ChordSeventhKind::Minor => 2,
            ChordSeventhKind::Sixth => 3
        };

        out = out * 10 + match self.fifth {
            ChordFifthKind::Skip => if self.seventh != ChordSeventhKind::Skip { 2 } else { 1 },
            ChordFifthKind::Diminished | ChordFifthKind::Augmented => 1,
            ChordFifthKind::Perfect => 0
        };

        out = out * 10 + match self.third {
            ChordThirdKind::Major | ChordThirdKind::Minor => 0,
            ChordThirdKind::Sus4 | ChordThirdKind::Sus2 => 1,
            ChordThirdKind::Skip => 2
        };

        out = out * 10 + self.permutation.num_cycles() as i32;
        out
    }

    pub fn to_string(&self) -> String {
        let mut out = String::new();
        // if we have neither third nor seventh..

        // if we have only third, then triad.


        // if we have only seventh, then (skip 3)

        // if we have both, the determine by 3rd and 7th.
        out.push_str(match self.third {
            ChordThirdKind::Major => "M",
            ChordThirdKind::Minor => "m",
            ChordThirdKind::Sus2 => "sus2",
            ChordThirdKind::Sus4 => "sus4",
            ChordThirdKind::Skip => "(skip 3)"
        });
        out.push_str(match self.fifth {
            ChordFifthKind::Perfect => "",
            ChordFifthKind::Diminished => " dim5",
            ChordFifthKind::Augmented => " aug5",
            ChordFifthKind::Skip => "(skip 5)"
        });
        out.push_str(match self.seventh {
            ChordSeventhKind::Major => " M7",
            ChordSeventhKind::Minor => " m7",
            ChordSeventhKind::Sixth => " 6",
            ChordSeventhKind::Skip => ""
        });
        out
    }
}

// sort in ascending order of badness
impl Ord for Chord {
  fn cmp(&self, other : &Chord) -> std::cmp::Ordering {
      self.badness().cmp(&other.badness())
  }
}

impl PartialOrd for Chord {
    fn partial_cmp(&self, other: &Chord) -> Option<std::cmp::Ordering> {
        self.badness().partial_cmp(&other.badness())
    }
}

// lookup table for chord.
#[derive(Clone, Debug)]
struct ChordLookupTable {
    pitch2chords : HashMap<Vec<i32>, BTreeSet<Chord>>
}

impl ChordLookupTable {
    fn generate(&mut self) {
        for third_kind in ChordThirdKind::enumerate() {
            for fifth_kind in ChordFifthKind::enumerate() {
                for seventh_kind in ChordSeventhKind::enumerate() {
                    let num_notes : usize = 1 + (third_kind != ChordThirdKind::Skip) as usize +
                            (fifth_kind != ChordFifthKind::Skip) as usize +
                            (seventh_kind != ChordSeventhKind::Skip) as usize;
                    for p in Permutation::generate(num_notes) {
                        for root in PitchClass::enumerate() {
                            let c = Chord {
                                third : third_kind,
                                fifth : fifth_kind,
                                seventh : seventh_kind,
                                permutation : p.clone(),
                            };
                            let iv = c.clone().materialize_at_root(root);
                            let entry = self.pitch2chords.entry(iv);
                            entry
                            .and_modify(|chords| { chords.insert(c.clone()); })
                            .or_insert(BTreeSet::from([c.clone()]));
                        }
                    }

                }
            }
        }

        println!("generated...");
        for (k, v) in self.pitch2chords.iter() {
            println!("{:?} -> {:?}", k, v);
        }
    }

    pub fn match_pitches(&self, pitches : Vec<Pitch>) -> Vec<Chord> {
        let mut out = Vec::new();
        for root in PitchClass::enumerate() {
            let key : Vec<i32> =
                pitches
                .iter()
                .map(|p| { (p.into_pitch_class() - root).pitch() as i32 })
                .collect();
            println!("looking up: {:?} / root: {:?} |  key {:?}", pitches, root, key);
            if let Some(chords) = self.pitch2chords.get(&key) {
                out.extend(chords.iter().cloned());
            };
        }
        out.sort();
        out
    }

    fn new() -> ChordLookupTable {
        let mut out = ChordLookupTable { pitch2chords: HashMap::new() };
        out.generate();
        out
    }
}


#[derive(Debug, PartialEq, Clone, Hash)]
pub enum NoteGroup {
    Single(PitchClass),
    Two(Interval),
    Chord (Vec<Chord>),
    Empty,
}

impl NoteGroup {
    // sorted list of notes, based on badness
    pub fn identify(ps : Vec<Pitch>, lut : &ChordLookupTable, _k : KeySignature) -> NoteGroup {
        if ps.is_empty() {
            NoteGroup::Empty
        } else if ps.len() == 1 {
            NoteGroup::Single(ps[0].into())
        } else if ps.len() == 2 {
            NoteGroup::Two(Interval::new(ps[0], ps[1]))
        } else {
            NoteGroup::Chord(lut.match_pitches(ps))
        }
    }
}

// This is synchronized with a PlayerTrack.
#[derive(Clone, Debug)]
pub struct ChordInfo {
    // map from y to notegroup for that y.
    note_groups : HashMap<u64, NoteGroup>,
    last_modified : LastModified,
    lut : ChordLookupTable,
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
            self.note_groups.insert(y, NoteGroup::identify(ps, &self.lut, k));
        }
    }

    pub fn get(&self, y : u64) -> &NoteGroup {
        assert!(y < TRACK_LENGTH);
        self.note_groups.get(&y).unwrap_or(&NoteGroup::Empty)
    }
}

impl Default for ChordInfo {
    fn default() -> ChordInfo {

        ChordInfo {
            note_groups: HashMap::new(),
            last_modified: LastModified::new(),
            lut: ChordLookupTable::new(),
        }
    }
}
