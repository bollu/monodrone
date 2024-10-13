#![allow(rustdoc::missing_crate_level_docs)] // it's an example
#![allow(dead_code)]




use serde::{Deserialize, Serialize};
 // 0.7.2
use tracing_subscriber::fmt::MakeWriter;

use std::path::PathBuf;

use std::sync::mpsc::channel;
use std::time::Duration;
use std::{fs::File};

use eframe::egui;
use egui::*;
use std::sync::Mutex;

use tracing::{event, Level};
use single_value_channel::channel_starting_with;
use std::thread::{self, sleep};


use crate::*;

fn audio_dir() -> PathBuf {
    let mut out = directories::UserDirs::new().unwrap().audio_dir().unwrap().to_path_buf();
    out.push("Monodrone");
    std::fs::create_dir_all(&out).unwrap();
    out
}

fn ide_image_file_path() -> PathBuf {
    let mut out = audio_dir();
    let filename = "monodrone-settings.ron";
    out.push(filename);
    out
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct IDEImageSaveInfo {
    contexts : Vec<Project>,
    ix : i32
}


// The image file, that has all the state.  #[derive(Debug, Serialize, Deserialize)]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(from = "IDEImageSaveInfo", into = "IDEImageSaveInfo")]
pub struct IDEImage {
    contexts : Vec<Project>,
    last_modified : LastModified,
    ix : i32,
    file_save_writer: single_value_channel::Updater<Option<(IDEImageSaveInfo, LastModified)>>
}

// spawn a thread that sleep for 500ms, polls the receiver, and if it finds
// data in the receiver, attempts to write the IDE image.
fn make_ide_image_saver_thread(mut receiver : single_value_channel::Receiver<Option<(IDEImageSaveInfo, LastModified)>>) {
    thread::spawn(move || {
        let mut last_modified = LastModified::default();
        loop {
            sleep(Duration::from_millis(500));

            let (image, latest_last_modified) = match receiver.latest() {
                None => continue,
                Some(x) => x
            };

            last_modified.union(latest_last_modified);
            if !last_modified.is_dirty() {
                continue;
            }
            last_modified.clean();

            // we have stuff to write, so write it.
            let path = ide_image_file_path();
            match File::create(path.clone()) {
                Ok(file) => {
                    let writer = file.make_writer();
                    match ron::ser::to_writer(writer, image) {
                        Ok(()) => {
                            event!(Level::INFO, "Successfully saved settings file to path {:?}", path.to_string_lossy());
                            last_modified.clean();
                        },
                        Err(e) => {
                            event!(Level::ERROR, "Failed to serialize image file to path {:?} with error {}",
                                path.to_string_lossy(), e);

                        }
                    }
                }
                Err(e) => {
                    event!(Level::ERROR, "Error creating image file '{}': {:?}", path.to_string_lossy(), e);
                }
            }
        };
    });
}

// This is a little subtle.
// When we load a save info from a file, we also spin up a channel
// to save the data from here on out.
impl From<IDEImageSaveInfo> for IDEImage {
    fn from(val: IDEImageSaveInfo) -> Self {
        let (mut receiver, updater) = single_value_channel::channel();
        make_ide_image_saver_thread(receiver);
        IDEImage {
            contexts : val.contexts,
            ix : val.ix,
            last_modified : Default::default(),
            file_save_writer: updater
        }
    }
}

impl From<IDEImage> for IDEImageSaveInfo {
    fn from(val : IDEImage) -> Self {
        IDEImageSaveInfo {
            contexts : val.contexts,
            ix : val.ix
        }
    }
}

impl IDEImage {
    pub fn ctx_mut(&mut self) -> &mut Project {
        &mut self.contexts[self.ix as usize]
    }

    // TODO: rename ctx to ctx_mut.
    pub fn ctx(&self) -> &Project {
        &self.contexts[self.ix as usize]
    }

    pub fn load() -> Self {
        let default = || {
            let (receiver, updater) = single_value_channel::channel();
            make_ide_image_saver_thread(receiver);
            IDEImage {
                contexts : vec![Project::new("track-0".to_string())],
                ix : 0,
                last_modified : LastModified::new(),
                file_save_writer: updater,
            }
        };
        let path = ide_image_file_path();
        let file =
            match File::open(path.clone()) {
                Ok(file) => {
                    event!(Level::INFO, "opened image file at '{}'", path.to_string_lossy());
                    file
                }
                Err(err) => {
                    event!(Level::ERROR, "error loading image file at '{}': {:?}", path.to_string_lossy(), err);
                    let mut d = default();
                    d.save();
                    return d
                }
            };

        let reader = std::io::BufReader::new(file);
        match ron::de::from_reader(reader) {
            Ok(image) => {
                event!(Level::INFO, "loaded image from file: {:?}", path);
                image
            }
            Err(err) => {
                event!(Level::ERROR, "failed to load image file: '{:?}'", err);
                let mut d = default();
                d.save();
                return d
            }
        }
    }

    pub fn new(&mut self) {
        let ix = self.contexts.len();
        let ctx = Project::new(format!("track-{}", ix));
        self.contexts.push(ctx);
        self.ix = ix as i32;
    }

    pub fn save(&mut self) {
        for ctx in &mut self.contexts {
            // TODO: make this a trait.
            self.last_modified.union(&ctx.last_modified);
        }

        // only save if we are both (a) dirty, and (b) have been idle for X seconds.
        if !self.last_modified.is_dirty_and_idle_for(Duration::from_secs(1)) {
            return;
        }

        // write into the updating channel.
        self.file_save_writer.update(Some((self.clone().into(), self.last_modified)));

        self.last_modified.clean();

    }

    pub fn switch_to(&mut self, ix: i32) {
        assert!(ix < self.contexts.len() as i32);
        assert!(ix >= 0);
        self.ix = ix;
    }
}


pub fn egui_project_picker(_ctx : &egui::Context, ui: &mut egui::Ui, image : &mut IDEImage) {
    ui.with_layout(Layout::top_down_justified(Align::Min), |ui| {
        let mut selected_ix : i32 = image.ix ;
        for (i, ctx) in image.contexts.iter().enumerate() {
            if ui.selectable_label(i == image.ix as usize, ctx.track_name.clone()).clicked() {
                selected_ix = i as i32;
            }
        }

        image.switch_to(selected_ix);
    });
}
