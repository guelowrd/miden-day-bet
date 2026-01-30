use anyhow::{Context, Result};
use miden_objects::account::AccountId;
use miden_objects::address::NetworkId;
use miden_objects::note::NoteFile;

fn main() -> Result<()> {
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "../note (38).mno".to_string());

    let note_file =
        NoteFile::read(&path).with_context(|| format!("Failed to read note file: {}", path))?;

    match note_file {
        NoteFile::NoteId(id) => {
            println!("NoteFile variant: NoteId");
            println!("Note ID: {}", id.to_hex());
        },
        NoteFile::NoteDetails { details, after_block_num, tag } => {
            println!("NoteFile variant: NoteDetails");
            println!("Note ID: {}", details.id().to_hex());
            println!("After block: {:?}", after_block_num);
            println!("Tag: {:?}", tag);
            println!("Assets:");
            for asset in details.assets().iter_fungible() {
                let faucet_id = asset.faucet_id();
                println!(
                    "  fungible: faucet={} (testnet={}) amount={}",
                    faucet_id.to_hex(),
                    faucet_id.to_bech32(NetworkId::Testnet),
                    asset.amount()
                );
            }
            for asset in details.assets().iter_non_fungible() {
                println!("  non-fungible: {:?}", asset);
            }
            let inputs = details.inputs().values();
            println!("Inputs ({}):", inputs.len());
            for (idx, felt) in inputs.iter().enumerate() {
                println!("  [{}] {}", idx, felt.as_int());
            }
            if inputs.len() >= 2 {
                match AccountId::try_from([inputs[0], inputs[1]]) {
                    Ok(id) => {
                        println!(
                            "Possible target account (testnet): {}",
                            id.to_bech32(NetworkId::Testnet)
                        );
                    },
                    Err(err) => {
                        println!("Inputs don't form a valid AccountId: {}", err);
                    },
                }
            }
        },
        NoteFile::NoteWithProof(note, _proof) => {
            println!("NoteFile variant: NoteWithProof");
            println!("Note ID: {}", note.id().to_hex());
            println!("Metadata tag: {:?}", note.metadata().tag());
            println!("Assets:");
            for asset in note.assets().iter_fungible() {
                let faucet_id = asset.faucet_id();
                println!(
                    "  fungible: faucet={} (testnet={}) amount={}",
                    faucet_id.to_hex(),
                    faucet_id.to_bech32(NetworkId::Testnet),
                    asset.amount()
                );
            }
            for asset in note.assets().iter_non_fungible() {
                println!("  non-fungible: {:?}", asset);
            }
            let inputs = note.inputs().values();
            println!("Inputs ({}):", inputs.len());
            for (idx, felt) in inputs.iter().enumerate() {
                println!("  [{}] {}", idx, felt.as_int());
            }
            if inputs.len() >= 2 {
                match AccountId::try_from([inputs[0], inputs[1]]) {
                    Ok(id) => {
                        println!(
                            "Possible target account (testnet): {}",
                            id.to_bech32(NetworkId::Testnet)
                        );
                    },
                    Err(err) => {
                        println!("Inputs don't form a valid AccountId: {}", err);
                    },
                }
            }
        },
    }

    Ok(())
}
