# Betting Project

A minimal Miden workspace for a single account contract (`betting-account`) and a note script
(`higher-than-seven-note`) with integration tests.

## **Installation**

Before getting started, ensure you have the following prerequisites:

1. **Install Rust** - Make sure you have Rust installed on your system. If not, install it from [rustup.rs](https://rustup.rs/)

2. **Install midenup toolchain** - Follow the installation instructions at: <https://github.com/0xMiden/midenup>

## **Structure**

```text
betting-project/
├── contracts/
│   ├── betting-account/         # Account contract with higher_than_seven
│   └── higher-than-seven-note/  # Note script that asserts result from note inputs
├── integration/                 # Integration crate (tests)
│   ├── src/
│   │   ├── helpers.rs           # Helper functions for building/testing
│   │   └── lib.rs
│   │   └── bin/                 # CLI-style helpers (deploy, sync, consume, inspect)
│   └── tests/                   # Test files
├── Cargo.toml                   # Workspace root
└── rust-toolchain.toml          # Rust toolchain specification
```

## **Design Philosophy**

This workspace follows a clean separation of concerns:

### **Contracts Folder - Miden Development**

The `contracts/` folder is your primary working directory when writing Miden smart contract code. Each contract is organized as its own individual crate, allowing for:

- Independent versioning and dependencies
- Clear isolation between different contracts
- Easy contract management and modularization

When you're working on Miden Rust code (writing smart contracts), you'll be working in the
`contracts/` directory.

### **Integration Crate - Scripts and Testing**

The `integration/` crate is used for compiling packages and running tests that exercise the
contract and note script together.

This structure provides flexibility as your application grows, allowing you to add custom dependencies, sophisticated tooling, and independent configuration specific to your deployment and testing needs.

> **Note**: The `helpers.rs` file inside the `integration/` crate exists to facilitate current
> development workflows.

## **Adding New Contracts**

To create a new contract crate, run the following command from the workspace root:

```bash
cargo miden new --account contracts/my-account
```

This will scaffold a new contract crate inside the `contracts/` directory with all the necessary boilerplate.

## **Testing Your Contracts**

Tests are located in `integration/tests/`. To add a new test:

1. Create a new test file in `integration/tests/` (e.g., `my_contract_test.rs`)
2. Write your test functions using the standard Rust testing framework
3. Run tests using the commands shown below

## **Commands**

### Compile a Contract

```bash
# Compile a specific contract
cargo miden build --manifest-path contracts/betting-account/Cargo.toml

# Or navigate to the contract directory
cd contracts/betting-account
cargo miden build
```

### Run Tests

```bash
# Navigate to integration crate and run tests
cd integration
cargo test                           # Run all tests
cargo test higher_than_seven_test    # Run specific test file
```

## **Deployment and Client Utilities**

The `integration/src/bin` tools are small CLI helpers for deploying accounts, syncing notes,
consuming notes, and checking balances. All commands below are run from the repo root unless
otherwise noted.

### Deploy a Hybrid Account (BasicWallet + betting component)

This account can receive faucet/public notes and still execute the betting logic.

```bash
cargo run -p integration --bin deploy_hybrid_account
```

The output prints both:
- the bech32 account address (with suffix) to receive notes, and
- the 16-byte hex account id (used by some APIs).

Always send notes to the bech32 address printed by the deploy command.

### Check Balance for a Faucet

```bash
# check_balance <account_bech32> <faucet_bech32>
cargo run -p integration --bin check_balance -- <account_addr> <faucet_addr>
```

### Sync Notes and List Matching Assets

```bash
# sync_list_notes <account_bech32> <faucet_bech32>
cargo run -p integration --bin sync_list_notes -- <account_addr> <faucet_addr>
```

### Consume a Private Note File

```bash
# consume_note_file <note_file> <account_bech32> <faucet_bech32>
cargo run -p integration --bin consume_note_file -- "note (41).mno" <account_addr> <faucet_addr>
```

### Inspect a Note File (shows faucet bech32 + hex)

```bash
# inspect_note_file <note_file>
cargo run -p integration --bin inspect_note_file -- "note (41).mno"
```

### Attempt to Consume Any Unspent Notes

```bash
# consume_unspent_notes <account_bech32> <faucet_bech32>
cargo run -p integration --bin consume_unspent_notes -- <account_addr> <faucet_addr>
```

## **Troubleshooting**

- Miden account IDs are 16 bytes in hex (shorter than the 32-byte recipient values you may see on explorers).
  If the recipient hex length does not match the account id printed at deploy time, the note was sent to a
  different account.
- If a public note shows as committed on the explorer but does not appear locally, run `sync_list_notes` and
  confirm you are using the correct bech32 account address.

## **Extending the Workspace**

If you need to extend the workspace with new crates (for example, to add libraries or additional tools), it is recommended to add these new crates in the root of the project directory. This helps keep the project structure clean and makes it easier to manage dependencies and workspace configuration.

To add a new crate to the workspace:

1. From the project root, run:
   ```bash
   cargo new my-new-crate
   ```
2. Then add the crate path (e.g., `my-new-crate`) to the `[workspace].members` section of your `Cargo.toml`.

**Note:** Avoid adding new crates as subdirectories under `contracts/` or `integration/`, unless they are intended to be contract crates or part of integration specifically. Keeping new crates at the root makes the project easier to understand and maintain.
