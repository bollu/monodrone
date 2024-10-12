use std::error::Error;
use std::thread::sleep;
use midir::{Ignore, MidiInput, MidiInputPort};
use std::io::stdin;
use tracing::{event, Level};


// represents a connection to an Op-z instance
struct Opz {
    // port : Option<MidiInputPort>, // MIDI input port.
    conn : Option<midir::MidiInputConnection<()>>,
}

impl Opz {
    fn new() -> Opz {
        event!(Level::INFO, "making new OP-Z.");

        Opz {
            // port: None,
            conn : None,

        }
    }

    fn find_port(&mut self) {
        event!(Level::INFO, "finding OP-Z...");

        let mut midi_in = MidiInput::new("midir reading input").unwrap();
        midi_in.ignore(Ignore::None);

        let in_ports = midi_in.ports();

        let mut port = None;
        for p in in_ports {
            if midi_in.port_name(&p).unwrap() == "OP-Z" {
                port = Some(p);
            }
        };

        self.conn = if let Some(p) = port {
            event!(Level::INFO, "found OP-Z!");
            midi_in.connect(
                &p,
                "midir-read-input",
                move |stamp, message, _| {
                    event!(Level::INFO, "message received from OP-Z. message: {:?}", message);
                    if message.len() <= 1 {
                        return;
                    }
                    println!("{}: {:?} (len = {})", stamp, message, message.len());
                },
                (),
            ).ok()
        } else {
            event!(Level::INFO, "Unable to find OP-Z.");
            None
        };

        // while true {
        //     sleep(core::time::Duration::from_secs(1));
        // };
    }
}

fn test_midi_in_op_z() -> Result<MidiInputPort, Box<dyn Error>> {
    let mut input = String::new();

    let mut midi_in = MidiInput::new("midir reading input")?;
    midi_in.ignore(Ignore::None);

    // Get an input port (read from console if multiple are available)
    let in_ports = midi_in.ports();
    let opz_opt = {
        let mut out = None;
        for port in in_ports {
            if midi_in.port_name(&port).unwrap() == "OP-Z" {
                out = Some(port);
            }
        }
        out
    };

    let opz = match opz_opt  {
        None => {
        event!(Level::INFO, "Unable to find OP-Z.");
        return Err("OP-Z not found".into());
        },
        Some(port) => {
            event!(Level::INFO, "found OP-Z!");
            port
        }
    };

    let _conn = midi_in.connect(
        &opz,
        "midir-read-input",
        move |stamp, message, _| {
            event!(Level::INFO, "message received from OP-Z. message: {:?}", message);
            if message.len() <= 1 {
                return;
            }
            println!("{}: {:?} (len = {})", stamp, message, message.len());
        },
        (),
    ).unwrap();


    input.clear();
    stdin().read_line(&mut input)?; // wait for next enter key press

    loop {
        sleep(core::time::Duration::from_secs(1));
    };

    // 463667691423: [181, 1/2/3/4, value]: 4 scroll wheels (len = 3)
    // keys: [149, 65...(key number), 0/100 up/down]: 65-69
    //
    // println!("Closing connection");
    // Ok(opz)
}

// TODO: implement file drag and drop with rl::IsFileDropped: https://github.com/raysan5/raylib/blob/master/examples/core/core_drop_files.c
