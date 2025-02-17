# Payment Channels

Proofgold has the infrastructure to support bidirectional payment
channels ([Poon Dryja 2016]), namely, multisig and hashed timelock
contracts (htlc).  Details are below.

## Multisig

Multisig addresses are p2sh addresses spendable by m signatures
corresponding to m-of-n public keys.  For payment channels, only
2-of-2 multisig addresses are used and these multisig addresses are
created using `createchannel` (described below). General multisig
addresses can be created by `createmultisig` or `addmultisig` (which
adds the p2sh address and redeem script to the wallet).

To create a multisig address, we need the n pubkeys. The easiest way
to obtain a pubkey is to use `getaddressinfo` for an address in the user's wallet.
For example, two different nodes with two different wallets could
use an address in each wallet:

* User 1:

```
getaddressinfo PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7
{"address":"p2pkh","pubkey":"0252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb7"}
```

* User 2:

```
getaddressinfo PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2
{"address":"p2pkh","pubkey":"02a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc7"}
```

Since the format for pubkeys is the same as in Bitcoin, a user could
also obtain the pubkey corresponding to a Bitcoin private key using
Bitcoin supporting software.  (Bitcoin private keys can be used to
sign Proofgold txs.)

After obtaining the 3 pubkeys any node can create a 2-of-3 multisig
address using the pubkeys. This is done as follows:

```
createmultisig 2 '["0252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb7","02a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc7"]'

P2sh address: PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL
Redeem script: 52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae
```

After creating the p2sh address, we might import it into the wallet
using `importp2sh` with the redeem script as follows:

```
importp2sh 52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae
Imported p2sh address: PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL
```

The two steps can be combined using `addmultisig`. If the address is imported
into the wallet, the node can recover the redeem script from the address:

```
getaddressinfo PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL
{"address":"p2sh","script":"52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae"}
```

Redeem scripts can also be explicitly given to commands like `signtx`
in case they are not in the wallet.

The multisig address PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL can be funded
using commands like `sendtoaddress`, `createtx` or `creategeneraltx`.
After funding the address, if the address is in the wallet
`printassets` can be used to see the assets at the address.
Here we explicitly give the ledger root for the Block 40106
since the example asset was spent after this block.

```
printassets e65c4a2d4a9c2a94e2fb6612c7ec3eaaef4b505aafa6717eecdc92dd3c51d92b
...
PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL:
86222deb5c1a163a32faf802f1f29420ed2186fd8eb3bf5e25c8e7fca4745dd9: (id b531f9e9d4c0ec6d41a1b57aebce30f3d098810afa32a5fb73df142fd295e5ea) [40080] Currency 2.0000000000 bars (200000000000 atoms)
...
```

Suppose we then wish to spend this asset. We can create the tx spending it as follows:

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"b531f9e9d4c0ec6d41a1b57aebce30f3d098810afa32a5fb73df142fd295e5ea"}]' '[{"addr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2","val":1.9999}]'

3b108091a5bf86535c03931a01fb6462482b05b9ae8dc94fa706666f0b0aadd55b77869987c60c54d09729dd9ffba67891ae2c5717570baff91a1bf39fad961635ae6d758773121e1b0000007081acca0104
```

This unsigned tx then needs to be signed by at least two of the
private keys.  Suppose *privkey1* is the private key for
PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 and *privkey2* is the private key for
PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2.  Suppose neither the redeem
script nor any of the privkeys are in the wallet. We can sign with the
first privkey by giving *privkey1* and the redeem script explicitly to
`signtx`.

```
signtx 3b108091a5bf86535c03931a01fb6462482b05b9ae8dc94fa706666f0b0aadd55b77869987c60c54d09729dd9ffba67891ae2c5717570baff91a1bf39fad961635ae6d758773121e1b0000007081acca0104 '["<privkey1>"]' '["52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae"]'

3b108091a5bf86535c03931a01fb6462482b05b9ae8dc94fa706666f0b0aadd55b77869987c60c54d09729dd9ffba67891ae2c5717570baff91a1bf39fad961635ae6d758773121e1b0000007081acca01b4060558be7950b248dd83369e3cebd68c70b597954bb8ecefe6d0f9079c8fbaf8eebe3a593a66195e2dfac260278355af75ec4bd14eefca172894ac6ad7612d8af68e3f28c5934cd772157c546a488152c97ac41e1da57de43963e2962afef0d7f8b9d9d3b7b819ecd596bbcd7f878d94ffcedb2105867efcbb356add24c9738ccf153ee58617c766bc2ed933f3fbffb1f60518b7ace8b8ed8f4b7505
Partially signed.
```

The partially signed tx can then be given to the controller of the second key
who can complete the signature. The redeem script is already part of the
partial signature and need not be given again.

```
signtx 3b108091a5bf86535c03931a01fb6462482b05b9ae8dc94fa706666f0b0aadd55b77869987c60c54d09729dd9ffba67891ae2c5717570baff91a1bf39fad961635ae6d758773121e1b0000007081acca01b4060558be7950b248dd83369e3cebd68c70b597954bb8ecefe6d0f9079c8fbaf8eebe3a593a66195e2dfac260278355af75ec4bd14eefca172894ac6ad7612d8af68e3f28c5934cd772157c546a488152c97ac41e1da57de43963e2962afef0d7f8b9d9d3b7b819ecd596bbcd7f878d94ffcedb2105867efcbb356add24c9738ccf153ee58617c766bc2ed933f3fbffb1f60518b7ace8b8ed8f4b7505 '[<privkey2>]'

3b108091a5bf86535c03931a01fb6462482b05b9ae8dc94fa706666f0b0aadd55b77869987c60c54d09729dd9ffba67891ae2c5717570baff91a1bf39fad961635ae6d758773121e1b0000007081acca01b4060558be7950b248dd83369e3cebd68c70b597954bb8ecefe6d0f9079c8fbaf8eebe3a593a66195e2dfac260278355af75ec4bd14eefca172894ac6ad7612d8af68e3f28c5934cd772151c14e0d29cc32f9bdd3a99e07ce3b0478ad50c32f5f3d72d71f34cfebbaad7aa5b9bab2e9871317ccebb53667cae39f76bc78ed71227885127f1bbeadb27ec2c316bc4e57bd3e64439d2ec51a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed515
Completely signed.
```

## Hashed timelock contracts

The other kind of p2sh address used in payment channels are hashed
timelock contracts (htlc). As with multisig addresses, more general
htlc addresses are supported than are required for payment channels.
The command `createhtlc` is used to create a htlc address.  By default
`createhtlc` creates a p2sh address payable after an relative lock
time (using the opcode OP_CSV, again analogous to the Bitcoin script
op code [BIP0068, BIP0112, BIP0113]), but can create an address
payable after an absolute time (using the opcode OP_CLTV, an opcode
analogous the Bitcoin script op code [BIP0065]) if the keyword
'absolute' is given. As with Bitcoin, absolute lock time refers to the
block height if it is less than 500000000 and refers to unix time
otherwise. In contrast to Bitcoin, relative lock time is always
measured in number of blocks since the asset was confirmed and
relative lock times must be less than 500000000. Payment channels are
assumed to use a relative lock time of 28 blocks (just over 1 day at average
block times).

We start by considering an example of an htlc with relative lock time
of 8 blocks.  We could explicitly give createhtlc a secret, but
without giving the secret the command will randomly generate one. A
secret must be 32 bytes given in hex.

```
createhtlc PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 8

P2sh address: Psa9bt1m4Lc6C2546LmuC3kUqezJ4iRQ4Eh
Redeem script: 6382012088a820b2ff39c6a31b0fc8ba6f51bce812fc26ecf7f0e5a621186cef0a47d80bb8e4438876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670408000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac
Secret: 939fac35f7d500b00b425c2191e521dba688490a17ae53be9386ff1870cea0a5
Hash of secret: b2ff39c6a31b0fc8ba6f51bce812fc26ecf7f0e5a621186cef0a47d80bb8e443
```

We could import the p2sh address into the wallet using `importp2sh` with the redeem script.

The redeem script gives two ways to spend an asset controlled by
Psa9bt1m4Lc6C2546LmuC3kUqezJ4iRQ4Eh. The IF branch is spendable by
a signature from PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 using the secret
939fac35f7d500b00b425c2191e521dba688490a17ae53be9386ff1870cea0a5.
The ELSE branch is spendable by PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2
8 blocks after the asset is confirmed.

A currency asset with 1 bar with assetid
01069a5b34016cac16570aa43364d7ffef3893e117e14120f367ff9caac81847 was
created at address Psa9bt1m4Lc6C2546LmuC3kUqezJ4iRQ4Eh by a tx in Block
40055.

After 8 blocks passed (after Block 40063) it was possible to
spend the asset by signing with *privkey2*, with 0.0001 as a tx fee.

```
createtx '[{"Psa9bt1m4Lc6C2546LmuC3kUqezJ4iRQ4Eh":"01069a5b34016cac16570aa43364d7ffef3893e117e14120f367ff9caac81847"}]' '[{"addr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2","val":0.9999}]'

9336f882fc3b9a6990b97c0a7dada1d5763e2f660b30d0dca2096063b5b852209d21bbfe7fc7990cbf080f02993ffbe75445c63812570baff91a1bf39fad961635ae6d758773121e1b000000b838f28e0204

signtx 9336f882fc3b9a6990b97c0a7dada1d5763e2f660b30d0dca2096063b5b852209d21bbfe7fc7990cbf080f02993ffbe75445c63812570baff91a1bf39fad961635ae6d758773121e1b000000b838f28e0204 '[<privkey2>]' '["6382012088a820b2ff39c6a31b0fc8ba6f51bce812fc26ecf7f0e5a621186cef0a47d80bb8e4438876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670408000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac"]'
```

Let us now consider an htlc with with a relative time of 48 blocks.

```
createhtlc PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 48

P2sh address: PsKUcuwfK1AosibZt3mbmU2PVpZaD2TBqot
Redeem script: 6382012088a8208d731fcc76af48733e26f3222327c7ce64f27f31c888ec830b89969fc79212ad8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670430000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac
Secret: ef231d76df4fc8e70d5b7a21a8c491c8f9b8b132f6e9077d1a79a76660d66f14
Hash of secret: 8d731fcc76af48733e26f3222327c7ce64f27f31c888ec830b89969fc79212ad
```

An asset worth 1 bar with id
6c7174eb862d9cb0ca5b93ec484ba041b49e6d8e644e50d77bd7fbb166d8c744
was created at address PsKUcuwfK1AosibZt3mbmU2PVpZaD2TBqot
in Block 40055.

This was then spent in Block 40080 (before 48 blocks had passed)
using the IF branch and the secret.

```
createtx '[{"PsKUcuwfK1AosibZt3mbmU2PVpZaD2TBqot":"6c7174eb862d9cb0ca5b93ec484ba041b49e6d8e644e50d77bd7fbb166d8c744"}]' '[{"addr":"PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7","val":0.9999}]'

8ba900ca9c0b4532fb20d72d531b5732675bf048608ba35b376ce18455de9a64475a020da2f56c73247382badebbde8f35c33e2612cd9900b22c4573780f71d373508aeb6e8f9d0114000000b838f28e0204

signtx 8ba900ca9c0b4532fb20d72d531b5732675bf048608ba35b376ce18455de9a64475a020da2f56c73247382badebbde8f35c33e2612cd9900b22c4573780f71d373508aeb6e8f9d0114000000b838f28e0204 '["<privkey1>"]' '["6382012088a8208d731fcc76af48733e26f3222327c7ce64f27f31c888ec830b89969fc79212ad8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670430000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac"]' '["ef231d76df4fc8e70d5b7a21a8c491c8f9b8b132f6e9077d1a79a76660d66f14"]'
```

After 48 blocks had passed, it would have been possible to sign
and spend with *privkey2*.

Let us see what happens if we try to sign with *privkey2*, the private
key for the second address PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 before
the 48 blocks had passed.  This corresponds to using the ELSE
branch. Signing was actually successful immediately (without waiting
the 48 blocks):

```
createtx '[{"PsKUcuwfK1AosibZt3mbmU2PVpZaD2TBqot":"6c7174eb862d9cb0ca5b93ec484ba041b49e6d8e644e50d77bd7fbb166d8c744"}]' '[{"addr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2","val":0.9999}]'

8ba900ca9c0b4532fb20d72d531b5732675bf048608ba35b376ce18455de9a64475a020da2f56c73247382badebbde8f35c33e2612570baff91a1bf39fad961635ae6d758773121e1b000000b838f28e0204

signtx 8ba900ca9c0b4532fb20d72d531b5732675bf048608ba35b376ce18455de9a64475a020da2f56c73247382badebbde8f35c33e2612570baff91a1bf39fad961635ae6d758773121e1b000000b838f28e0204 '[<privkey2>]' '["6382012088a8208d731fcc76af48733e26f3222327c7ce64f27f31c888ec830b89969fc79212ad8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670430000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac"]'

8ba900ca9c0b4532fb20d72d531b5732675bf048608ba35b376ce18455de9a64475a020da2f56c73247382badebbde8f35c33e2612570baff91a1bf39fad961635ae6d758773121e1b000000b838f28e02b406054832fac9ce0b313ea41eb3a85da907ff5f7f4d1827dfaee47b3a850c3b6a6e805d6742752d9e69e7ef1ae356fc4b1fe354e202d1e3e7991929f589396f923f9f37ef54ce703dc7b61d5260e8c7bf5ba3d64d923cc7f85ce1536e78716cc6eb923d33bfff1f6b5f8071cb8a8edbfe3840a661c70a0e0812316a908de77e646ef735d2b93e4dce1739f2e471e764e5ff8d891c31fbc10b135bfe7c5cb2c4d688eda6a6a8796640b259159b87ef51bce9f3a0295eefee71e740946709c2040810a0ecba765353746dd1ebfc9a36cdffdcdab2a55aaedbd53b3c4f92a74db4885901
Completely signed.
```

However `validatetx` indicated that the tx was not yet valid:

```
validatetx 8ba900ca9c0b4532fb20d72d531b5732675bf048608ba35b376ce18455de9a64475a020da2f56c73247382badebbde8f35c33e2612570baff91a1bf39fad961635ae6d758773121e1b000000b838f28e02b406054832fac9ce0b313ea41eb3a85da907ff5f7f4d1827dfaee47b3a850c3b6a6e805d6742752d9e69e7ef1ae356fc4b1fe354e202d1e3e7991929f589396f923f9f37ef54ce703dc7b61d5260e8c7bf5ba3d64d923cc7f85ce1536e78716cc6eb923d33bfff1f6b5f8071cb8a8edbfe3840a661c70a0e0812316a908de77e646ef735d2b93e4dce1739f2e471e764e5ff8d891c31fbc10b135bfe7c5cb2c4d688eda6a6a8796640b259159b87ef51bce9f3a0295eefee71e740946709c2040810a0ecba765353746dd1ebfc9a36cdffdcdab2a55aaedbd53b3c4f92a74db4885901
Tx is not valid until block height 40103
Tx is valid and has id fe11be82b6d63cea8ae0022f6529fd918c8563164eb9cf18cd9a29fab1640735
Tx is supported by the current ledger and has fee 0.0001 bars (above minrelayfee 0.0000308 bars)
```

Likewise, `sendtx` would refuse to send the tx until Block 40102 had been staked,
and peers would not accept it if it were sent before Block 40102.

## Creating a payment channel

We now use multisig and htlc to create bidirectional payment channels.
The `createchannel` command can be used to obtain the initial about
the channel including a 2-of-2 multisig address (the *fund address*)
and redeem script, an unsigned funding tx and two asset ids (*fund
asset ids*) that will be held at the fund address if the funding tx is
signed and confirmed.

Let Alice and Bob be the two parties. Suppose Alice controls pubkey
0252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb7
with private key *AlicePrivKey*
and Bob controls pubkey 02a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc7
with private key *BobPrivKey*.
Alice's corresponding address is PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7
and Bob's corresponding address is PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2.
Suppose also that Alice controls a currency asset
with asset id
c7745412bc166768dde3d2551afa060adf886925184556e6fed28643134536b0
with more than 0.6 bars
and Bob controls a curency asset with asset id
730204fc4bd7dcb24368254ec4650459f2e4878bb85dfbaf7e1320cadd62332f
with more than 0.4 bars.
A payment channel with Alice controling 0.6 bars
and Bob controlling 0.4 bars can be initialized as follows:

```
createchannel 0252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb7 02a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc7 c7745412bc166768dde3d2551afa060adf886925184556e6fed28643134536b0 730204fc4bd7dcb24368254ec4650459f2e4878bb85dfbaf7e1320cadd62332f 0.6 0.4

Funding tx: d19c0920cb523487f710373d07a5b8eef6d8194039a6a392e0b53843eb1e97aed2d03750f8464c2bc128b232f797361c9a28b2818dab85d77c8d8df9cf564b8b1ad7b6bac339098fcd9c0001ffd235b7ec105a8913711941963cf9e1226ed7feabdf048872b7d8cc8b1d08c0c8d25fc329ae81498d807d3231a495825c0300004003fe1116c00e046064e9afe114d7c0a446c03e9918d24a41ae0100002001ea0512209a330164598ae6f01ee2a6e7a014d7dd1e3b032800000090e0e43f0610570baff91a1bf39fad961635ae6d758773121e1b00000068b8b7580100
Fund 2-of-2 address: PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL
Redeem script: 52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae
Fund asset id 1: ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258
Fund asset id 2: d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316
```

Alice and Bob can import the p2sh funding address into their wallets.

```
importp2sh 52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae
```

The fundingtx spends Alice's current asset and Bob's current asset together to
create two fund assets (which will have the two fund asset ids) which together
add to 0.6+0.4 = 1 bar, and will return Alice's change to her address
and Bob's change to his address.

Both Alice and Bob must sign the funding tx before it can be confirmed.
Before doing so, both Alice and Bob must create and sign initial commitment txs.

Alice creates an initial commitment tx which Bob must sign and give back.
Alice first creates the htlc: `createhtlc <Bob> <Alice> 28 relative`.
This address will be spendable by Bob if Bob has the secret
and will be spendable by Alice 28 blocks after confirmation.

```
createhtlc PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 28

P2sh address: PsSXm6sMGzjN7VK9X95H7tQnBsMctRHJjXf
Redeem script: 6382012088a820e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad8876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c3667041c000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac
Secret: 14b91e631e0c4ccebb0981af9131cad331b2f2cea70eff54a9e947286dde5ce9
Hash of secret: e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad
```

Here the secret is Alice's first secret.

Alice now creates her first commitment tx.  Loosely speaking, the
commitment tx spends the two (hypothetical) fund assets to send 0.5999
bars (0.6 minus a txfee) to her htlc address and 0.3999 bars
(0.4 minus a txfee) to Bob's p2pkh address.  To be more precise, the
commitment tx will spend the two fund assets from the fund asset
address to create two new currency assets still held at the fund
address.  However, the two new currency assets will be spendable by
different "lock addresses". The 0.5999 asset will be spendable by
Alice's htlc address and the 0.3999 asset will be spendable by Bob's
p2pkh address.  There is a technical reason for this approach.
Proofgold addresses are not allowed to hold more than 34 assets.
Because of this, a commitment tx might be made invalid by a third
party who fills the intended recipient address with 34 assets.  To
avoid this attack, we create two fund assets for the payment channel
held at the multisig fund address (taking up 2 of the potential 34
assets) and always have commitment txs spend the 2 assets and create 2
new assets at the same address (ensuring that the commitment txs will
never result in more than 34 assets being held at an address).

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.5999,"lockheight":0,"lockaddr":"PsSXm6sMGzjN7VK9X95H7tQnBsMctRHJjXf"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.3999,"lockheight":0,"lockaddr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2"}]'

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cef6777d3f4c409b61a5802c23788dd0e0e5594d10500000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c7060000000000000000000000129e2cf30101
```

Alpha sends this unsigned commitment tx along with the hash of her secret to Bob.
Bob can verify it is correct using the command `verifycommitmenttx`

```
verifycommitmenttx PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258 d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316 0.5999 0.3999 e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad 28 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cef6777d3f4c409b61a5802c23788dd0e0e5594d10500000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c7060000000000000000000000129e2cf30101

Valid commitment tx for PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7
```

Since this is a valid commitment tx for Alice, Bob signs it and returns it to Alice.
Bob cannot use `signtx` for this purpose since the assets being spent are not in the ledger.
However, the command `simplesigntx` can be used to sign it, since it makes certain simplifying
assumptions about assets being spent by the tx.

```
simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cef6777d3f4c409b61a5802c23788dd0e0e5594d10500000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c7060000000000000000000000129e2cf30101 '["<BobPrivKey>"]' '["6382012088a820e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad8876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c3667041c000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cef6777d3f4c409b61a5802c23788dd0e0e5594d10500000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c7060000000000000000000000129e2cf301ad4101ee0eb899ac459034657e75c973f8decec1b75af43dbdeafbf7c7d9468c0a1225ec820d75cf547a1e6972c7fc198edfcc513d6b8ccfc95b14d97bf54db2a801360cecbf2445894b1f1e951a52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff3764881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe3525d1d00
```

Bob then passes this back to Alice who checks if it is the same
commitment tx and if it is signed by Bob. There is no Proofgold
command for checking this partial signature, but Alice can check Bob's
signature by temporarily signing the tx with *AlicePrivKey* and
ensuring that the resulting tx is completely signed.

The procedure is then repeated interchanging the roles of Alice and Bob.

Bob creates an htlc and initial commitment tx.

```
createhtlc PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 28

P2sh address: PsKQr5q3SjpbicAB4Gt149HjDyBJUmqnven
Redeem script: 6382012088a820f7bdb242c5dc061116d3ad9219ee75307ca2cb0e05db9db22c386a42caa99ffc8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b032867041c000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac
Secret: 5617b0a6d1a3c7370f412ce2bcd48ca088c540ae904b2f11d0fc699c3118d53e
Hash of secret: f7bdb242c5dc061116d3ad9219ee75307ca2cb0e05db9db22c386a42caa99ffc

createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.5999,"lockheight":0,"lockaddr":"PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.3999,"lockheight":0,"lockaddr":"PsKQr5q3SjpbicAB4Gt149HjDyBJUmqnven"}]'

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825ca739134096a5680eef216e7a0e4a71ddedb133800200000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b91ec6abf224a615fe8c816c2a5d52c999ca0216db020000000000000000000000129e2cf30101
```

Bob sends this tx to Alice along with the hash of his secret. She verifies it and signs it
and sends the partially signed tx back to Bob, who doublechecks the result.

```
verifycommitmenttx PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258 d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316 0.5999 0.3999 f7bdb242c5dc061116d3ad9219ee75307ca2cb0e05db9db22c386a42caa99ffc 28 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825ca739134096a5680eef216e7a0e4a71ddedb133800200000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b91ec6abf224a615fe8c816c2a5d52c999ca0216db020000000000000000000000129e2cf30101

Valid commitment tx for PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2

simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825ca739134096a5680eef216e7a0e4a71ddedb133800200000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b91ec6abf224a615fe8c816c2a5d52c999ca0216db020000000000000000000000129e2cf30101 '["<AlicePrivKey>"]' '["52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae"]'

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825ca739134096a5680eef216e7a0e4a71ddedb133800200000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b91ec6abf224a615fe8c816c2a5d52c999ca0216db020000000000000000000000129e2cf301ad41017a86cc76e54dca1f7f23c6df9b2658f73879520d0e59f96f807939570daa503ffeaa9cf532c77fbe26c599c60316e65c71be68b4c26faa3c88f53be493cb9957b57ef66454d286e31f951a52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff3764881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe3525d1d00
```

Once both parties have partially signed commitment txs, they both sign the funding tx
and send it to be confirmed. In this example, the funding tx was confirmed
at height 40173, creating two fund assets.

```
printassets
...
Possibly controlled p2sh assets:
PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL:
826f1b088cd6942e39de93a3d6324397e50075320199df6fa60dbfd12323efea: (id d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316) [40173] Currency 0.4 bars (40000000000 atoms)
68204be64eca2193c787b5f998d33dffe358f28e4cb6b4555e7b68ed117380ea: (id ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258) [40173] Currency 0.6 bars (60000000000 atoms)
...
```

The payment channel is open as long as these assets remain unspent.
The only way to spend either of the assets is with a tx signed by
both Alice and Bob, and initially the only way of obtaining
such a tx is by having one party sign a commitment tx already signed
by the other party. According to the commitment txs, the current balance
of the channel is:

* Alice: 0.5999

* Bob: 0.3999

Note: If only one party is funding the channel, then assume that party
is Alice and use the command `createchannelonefunder`.

## Updating a payment channel

Suppose Alice decides to send 0.3 bars to Bob along the payment
channel. Assume the current balance is still the initial balance
reflected by the initial commitment txs:

* Alice: 0.5999

* Bob: 0.3999

Alice and Bob follow a protocol to exchange new commitment txs
and revoke previous commitment txs to reflect a new balance:

* Alice: 0.2999

* Bob: 0.6999

We walk through a 4 step protocol to make this update.

1. Alice creates a new commitment tx which is given to Bob, Bob signs
and gives back to Alice.

First Alice creates a new htlc with a new secret.

```
createhtlc PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 28

P2sh address: PsPDcBMvqAAxAk9hJ3mGnmEeP7U8s9M97ey
Redeem script: 6382012088a820e5f354d3cae6016db7fd49a22ea4eca52c0e48b76dc08298a11c94f911534e718876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c3667041c000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac
Secret: cd6fd78558495b0b17399eaab1f5100ffe6326c140d95d9eedc04d84b0bba5fb
Hash of secret: e5f354d3cae6016db7fd49a22ea4eca52c0e48b76dc08298a11c94f911534e71
```

Alice creates a new commitment tx which would create two new assets
held at the fund address with 0.2999 controlled by Alice's htlc
address and 0.6999 controlled by Bob's p2pkh address.

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.2999,"lockheight":0,"lockaddr":"PsPDcBMvqAAxAk9hJ3mGnmEeP7U8s9M97ey"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.6999,"lockheight":0,"lockaddr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2"}]'

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cafe5718e2371876686f4152bfe7849f708c2af0c04000000000000000000000006fb8b15803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c70600000000000000000000002096744b0101
```

Alice passes this unsigned tx to Bob and the hash of the new
secret. Bob verifies the commitment tx:

```
verifycommitmenttx PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258 d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316 0.2999 0.6999 e5f354d3cae6016db7fd49a22ea4eca52c0e48b76dc08298a11c94f911534e71 28 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cafe5718e2371876686f4152bfe7849f708c2af0c04000000000000000000000006fb8b15803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c70600000000000000000000002096744b0101

Valid commitment tx for PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7
```

Bob then signs it and sends the partially signed commitment tx back to
Alice.  Bob can either use `simplesigntx` or `signtx` for this.
If Bob has imported the p2sh script into his wallet and
the private key is in his wallet, `signtx` with no extra arguments
should work.

```
signtx 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cafe5718e2371876686f4152bfe7849f708c2af0c04000000000000000000000006fb8b15803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c70600000000000000000000002096744b0101

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cafe5718e2371876686f4152bfe7849f708c2af0c04000000000000000000000006fb8b15803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c70600000000000000000000002096744b01ad41013224ff79f0f79686d55bc7cb9ca6f7d3795f53543bdc3a7e8ccfd973cc78f0b15df2d14937353a7befeee3a3758a85db96ef5392b3d3f74f0cdfffc3e28cbdf3bf2c7937f2fb87571f951a52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff3764881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe3525d1d00
```

2. Bob creates a new commitment tx which is given to Alice, Alice
signs and gives back to Bob.

First Bob creates a new htlc address with a new secret.

```
createhtlc PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 28

P2sh address: PsbnHXZqa81wvJNLxpqg9qzRNT38xwkV5wx
Redeem script: 6382012088a8208ce308b57b0bc61321c85b69d2a889a50c2a8726ede8e853251c5052a9301b1d8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b032867041c000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac
Secret: 6332dbbca4da5112f1bb2d62ae1251fbacc2ba9c62ab8c15da9cdedd37ed27a4
Hash of secret: 8ce308b57b0bc61321c85b69d2a889a50c2a8726ede8e853251c5052a9301b1d
```

Bob creates a new commitment tx which would create two new assets held
at the fund address with 0.2999 controlled by Alice's p2pkh address
and 0.6999 controlled by Bob's new htlc address.

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.2999,"lockheight":0,"lockaddr":"PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.6999,"lockheight":0,"lockaddr":"PsbnHXZqa81wvJNLxpqg9qzRNT38xwkV5wx"}]'

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825ca739134096a5680eef216e7a0e4a71ddedb1338002000000000000000000000006fb8b15803b108091a5bf86535c03931a01fb6462482b05b97edc3d527bfac358996cf0e3ae46aeac5ddb3b450500000000000000000000002096744b0101
```

Bob passes this new unsigned commitment tx along with the hash of the new secret to 
Alice. Alice verifies the new commitment:

```
verifycommitmenttx PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL ccacef0902b35622569fedc6b338406e2d30fa0ae691aa1417c5c13df0dd8258 d9f806bec32f9023f61495d042c607d63ad615a90b402a080dc020f5b9d7b316 0.2999 0.6999 8ce308b57b0bc61321c85b69d2a889a50c2a8726ede8e853251c5052a9301b1d 28 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825ca739134096a5680eef216e7a0e4a71ddedb1338002000000000000000000000006fb8b15803b108091a5bf86535c03931a01fb6462482b05b97edc3d527bfac358996cf0e3ae46aeac5ddb3b450500000000000000000000002096744b0101

Valid commitment tx for PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2
```

She then signs it and returns it to Bob.

3. Alice gives her previous secret to Bob, ensuring she will not use
the previous commitment tx.

Specifically Alice gives Bob the secret
14b91e631e0c4ccebb0981af9131cad331b2f2cea70eff54a9e947286dde5ce9
Bob can verify this is the secret easily as follows:

```
hashsecret 14b91e631e0c4ccebb0981af9131cad331b2f2cea70eff54a9e947286dde5ce9

e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad
```

Using this secret, Bob could spend the output intended for Alice if
she sends her prevous commitment tx.

4. Bob gives his previous secret to Alice, ensuring he will not use
the previous commitment tx.

Specifically, Bob sends Alice 5617b0a6d1a3c7370f412ce2bcd48ca088c540ae904b2f11d0fc699c3118d53e
which she verifies:

```
hashsecret 5617b0a6d1a3c7370f412ce2bcd48ca088c540ae904b2f11d0fc699c3118d53e

f7bdb242c5dc061116d3ad9219ee75307ca2cb0e05db9db22c386a42caa99ffc
```

At this point the only commitment txs that can be used without
penalty are the most recent ones.

Of course, Bob could also send bars to Alice in an analogous
way by reversing the roles of Alice and Bob above.

## Closing a payment channel

A payment channel can be closed by either party at any time without
penalty by sending the most recent commitment tx.  The party that
sends the commitment tx will need to wait 28 blocks to retrieve the
funds from the asset controlled by the htlc address.

Alternatively, the two parties can always sign a new tx spending both
the fund assets with the latest balances directly to p2pkh addresses
controlled by the two parties.

In this example suppose Alice tries to take back the 0.3 bars by
signing and publishing the original commitment tx. This is something
one would expect her not to be able to do since she has allegedly sent
the 0.3 to Bob already. Yet she can do this by completing the
signature for the original commitment tx and sending it. (She will
be punished for this after the tx confirms.)

```
signtx 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cef6777d3f4c409b61a5802c23788dd0e0e5594d10500000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c7060000000000000000000000129e2cf301ad4101ee0eb899ac459034657e75c973f8decec1b75af43dbdeafbf7c7d9468c0a1225ec820d75cf547a1e6972c7fc198edfcc513d6b8ccfc95b14d97bf54db2a801360cecbf2445894b1f1e951a52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff3764881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe3525d1d00

3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cef6777d3f4c409b61a5802c23788dd0e0e5594d10500000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c7060000000000000000000000129e2cf301ad4101de6edb756dffd6007f4b0f5b9bebff8a4203bb8f7fbbbcf0e90b2107acd8516ce0e9dc018fa7ceb47f7fcd3b8bd28e3f58aa6cda0bab2efe3b5167faa381ef4a749ab1b96a9ca08b0605b83be066b21641d294f9d525cfe17b3b07df6ad1f7f4aaefdf1f671b312a4894b00b36d43d53e979a4c91df367387e3347f5ac313e276f5164efd537c9a206d830b0ff9214252e7d78546a488152c97ac41e1da57de43963e2962afef0d7f8b9d9d3b7b819ecd596bbcd7f878d94ffcedb2105867efcbb356add24c9738ccf153ee58617c766bc2ed933f3fbffb1f60518b7ace8b8ed8f4b75b50605b859ecd6a64c9f2e0e0b352edae7630dfbeefd3b6462bdbd390a7ece3c2ec2bb3111e7e6fdda764fd44ce73b444a752370a5717d6a459d34e3c6f6d5d5127ddf37f2d7bfdcadba1d1a14e0ee809bc95a044953e657973c87efed1c7cab45dfd3abbe7f7f9c6dc4a82051c22ed850f74ca5e7912677cc9fe1f8cd1cd5b3c6f89cbc4591bd57df248b1a60c3c0fe4b5294b8f4e151a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed515

Completely signed.

sendtx 3b108091a5bf86535c03931a01fb6462482b05b966667d4f1098b512b1fa6c379ec501726b81d157308f54a5b8280eee81ef16c4da81008c2cfd359ce21a98d408d82713435a29c87536be81eff00be4883d4525b490f181b58e7545ea02900a420330487deef5ac851d08c0c8d25fc329ae81498d807d3231a495825cef6777d3f4c409b61a5802c23788dd0e0e5594d10500000000000000000000000df7aec1803b108091a5bf86535c03931a01fb6462482b05b9ced5c26bbec6c6fc67aba5458d6b5bdde19c84c7060000000000000000000000129e2cf301ad4101de6edb756dffd6007f4b0f5b9bebff8a4203bb8f7fbbbcf0e90b2107acd8516ce0e9dc018fa7ceb47f7fcd3b8bd28e3f58aa6cda0bab2efe3b5167faa381ef4a749ab1b96a9ca08b0605b83be066b21641d294f9d525cfe17b3b07df6ad1f7f4aaefdf1f671b312a4894b00b36d43d53e979a4c91df367387e3347f5ac313e276f5164efd537c9a206d830b0ff9214252e7d78546a488152c97ac41e1da57de43963e2962afef0d7f8b9d9d3b7b819ecd596bbcd7f878d94ffcedb2105867efcbb356add24c9738ccf153ee58617c766bc2ed933f3fbffb1f60518b7ace8b8ed8f4b75b50605b859ecd6a64c9f2e0e0b352edae7630dfbeefd3b6462bdbd390a7ece3c2ec2bb3111e7e6fdda764fd44ce73b444a752370a5717d6a459d34e3c6f6d5d5127ddf37f2d7bfdcadba1d1a14e0ee809bc95a044953e657973c87efed1c7cab45dfd3abbe7f7f9c6dc4a82051c22ed850f74ca5e7912677cc9fe1f8cd1cd5b3c6f89cbc4591bd57df248b1a60c3c0fe4b5294b8f4e151a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed515

e2f6058800f1b92ffa1e3ba5f53c996c98db8fbfe8d9c087b1f569f2dc29ff18
```

The tx e2f6058800f1b92ffa1e3ba5f53c996c98db8fbfe8d9c087b1f569f2dc29ff18
was confirmed in Block 40239. Afterwards, the assets held at the fund
address PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL were:

```
PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL:
72734ff621644c6834cbe52bc0b278d30fbdd64c675f0b5cb9d0990ccaed47ef: (id fed9701c0cb62f536033e79a321a0c1fb122c068502009684eab3dfbd61042cd) [40239] Currency 0.3999 bars (39990000000 atoms)
97222e6868419e2a0c2bd3760fdff3796d20d91e3dcaab9a03e9f8b4502cab63: (id 27d2263c2b7fa4dbeec021c4dd701ca87d420c863e1a2d14d2a5dbaf867dbead) [40239] Currency 0.5999 bars (59990000000 atoms)
```

The asset with 0.3999 is controlled by Bob:

```
query 72734ff621644c6834cbe52bc0b278d30fbdd64c675f0b5cb9d0990ccaed47ef

{"response":"known","dbdata":[{"type":"asset","assethash":"72734ff621644c6834cbe52bc0b278d30fbdd64c675f0b5cb9d0990ccaed47ef","assetid":"fed9701c0cb62f536033e79a321a0c1fb122c068502009684eab3dfbd61042cd","bday":40239,"obligation":{"type":"obligation","lockaddress":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2","lockheight":0,"reward":false},"preasset":{"type":"preasset","preassettype":"currency","val":{"atoms":39990000000,"bars":"0.3999"}}}]}
```

The asset with 0.5999 is controlled by Alice's first htlc address, the
one Bob for which the secret
14b91e631e0c4ccebb0981af9131cad331b2f2cea70eff54a9e947286dde5ce9.

```
query 97222e6868419e2a0c2bd3760fdff3796d20d91e3dcaab9a03e9f8b4502cab63

{"response":"known","dbdata":[{"type":"asset","assethash":"97222e6868419e2a0c2bd3760fdff3796d20d91e3dcaab9a03e9f8b4502cab63","assetid":"27d2263c2b7fa4dbeec021c4dd701ca87d420c863e1a2d14d2a5dbaf867dbead","bday":40239,"obligation":{"type":"obligation","lockaddress":"PsSXm6sMGzjN7VK9X95H7tQnBsMctRHJjXf","lockheight":0,"reward":false},"preasset":{"type":"preasset","preassettype":"currency","val":{"atoms":59990000000,"bars":"0.5999"}}}]}
```

As a result Bob can spend both assets. He needs to spend the second
asset within 28 blocks since Alice would be able to spend it after 28
blocks.

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"fed9701c0cb62f536033e79a321a0c1fb122c068502009684eab3dfbd61042cd"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"27d2263c2b7fa4dbeec021c4dd701ca87d420c863e1a2d14d2a5dbaf867dbead"}]' '[{"addr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2","val":0.9997}]'

3b108091a5bf86535c03931a01fb6462482b05b9f6cf86e360b07d99029b39d794d160f88815014683024940735aedd9b786106ade81008c2cfd359ce21a98d408d82713435a29c8f589b409cfca1fe9b63b700871371c076a9f1083a18f460b8574e9f6ab619f6fabb85a78cdd7d898ff6cb5b4a8716dab3b9c93f0d8000000c085512b092000
```

To sign the tx, Bob needs the redeem script for Alice's first htlc
address.  Bob can easily regenerate this using the secret. (In fact,
the redeem script can be recovered with only the hash of the secret
and this is done internally by the `verifycommitmenttx` command. If a
user wanted the redeem script without the secret, the code could be
modified to print the redeem script when running
`verifycommitmenttx`.)

```
createhtlc PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 28 14b91e631e0c4ccebb0981af9131cad331b2f2cea70eff54a9e947286dde5ce9

P2sh address: PsSXm6sMGzjN7VK9X95H7tQnBsMctRHJjXf
Redeem script: 6382012088a820e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad8876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c3667041c000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac
Secret: 14b91e631e0c4ccebb0981af9131cad331b2f2cea70eff54a9e947286dde5ce9
Hash of secret: e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad
```

Bob signs and sends the tx, taking all the funds.

```
signtx 3b108091a5bf86535c03931a01fb6462482b05b9f6cf86e360b07d99029b39d794d160f88815014683024940735aedd9b786106ade81008c2cfd359ce21a98d408d82713435a29c8f589b409cfca1fe9b63b700871371c076a9f1083a18f460b8574e9f6ab619f6fabb85a78cdd7d898ff6cb5b4a8716dab3b9c93f0d8000000c085512b092000 '["<BobPrivKey>"]' '["6382012088a820e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad8876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c3667041c000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac"]' '["14b91e631e0c4ccebb0981af9131cad331b2f2cea70eff54a9e947286dde5ce9"]'

3b108091a5bf86535c03931a01fb6462482b05b9f6cf86e360b07d99029b39d794d160f88815014683024940735aedd9b786106ade81008c2cfd359ce21a98d408d82713435a29c8f589b409cfca1fe9b63b700871371c076a9f1083a18f460b8574e9f6ab619f6fabb85a78cdd7d898ff6cb5b4a8716dab3b9c93f0d8000000c085512b09a0f1b83d4eb42c0ea00febff9ed953f23a63eca281129e2b9e839c4417b5f5f7315435d49d6d0301c463ea63c3bf73e322754d340c2ac1ed9310d15d615d6d011927143bb03fb132436ed6dcc37efa3bd91594bc7bacbe8f4d4a75ef838e34f1f63878b406ebbd75f264b255f653fd0d455906ea436fcd3f7590f3ebdd1ae78d99d41a14606ae8493b1e4cfa1eac5cfa9b9717af7fd8efd580dad7226e4a577855b181a1826688f6fb6bc7af852a8e7b3133c69f7d952a34fa5e6f5fd06f5d22473b7abf48fab23b5f74eaf3644881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe32029e6f638d62343a6ce77270cfc3a724ce5d363ca96effcb4c3ff5453a73f8ab2ad77aee9a3320d3b5670409088518314efb47249ce70e77fcd4fde6bd58b3cf97bff6ad8666bc5f285f60e281abfdf8c5479b6466c373545d716bdceaf69d3fccfad2d5baae5ba5dbdc3f32479da3c4b902340800065d7b59b9aa2e69901c966556c1ebe47f1a6cf83a678bdbbc79d0351a245cc0a

sendtx 3b108091a5bf86535c03931a01fb6462482b05b9f6cf86e360b07d99029b39d794d160f88815014683024940735aedd9b786106ade81008c2cfd359ce21a98d408d82713435a29c8f589b409cfca1fe9b63b700871371c076a9f1083a18f460b8574e9f6ab619f6fabb85a78cdd7d898ff6cb5b4a8716dab3b9c93f0d8000000c085512b09a0f1b83d4eb42c0ea00febff9ed953f23a63eca281129e2b9e839c4417b5f5f7315435d49d6d0301c463ea63c3bf73e322754d340c2ac1ed9310d15d615d6d011927143bb03fb132436ed6dcc37efa3bd91594bc7bacbe8f4d4a75ef838e34f1f63878b406ebbd75f264b255f653fd0d455906ea436fcd3f7590f3ebdd1ae78d99d41a14606ae8493b1e4cfa1eac5cfa9b9717af7fd8efd580dad7226e4a577855b181a1826688f6fb6bc7af852a8e7b3133c69f7d952a34fa5e6f5fd06f5d22473b7abf48fab23b5f74eaf3644881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe32029e6f638d62343a6ce77270cfc3a724ce5d363ca96effcb4c3ff5453a73f8ab2ad77aee9a3320d3b5670409088518314efb47249ce70e77fcd4fde6bd58b3cf97bff6ad8666bc5f285f60e281abfdf8c5479b6466c373545d716bdceaf69d3fccfad2d5baae5ba5dbdc3f32479da3c4b902340800065d7b59b9aa2e69901c966556c1ebe47f1a6cf83a678bdbbc79d0351a245cc0a

f3317769b9e64bcaae1002b82d6d13ae4a19d8dba0667bf7bf6fb2cf93e4e520
```

This tx was sent when the current block height was 40269,
which was already after the previous transaction had 28 confirmations,
even though it was less than 24 hours since the previous transaction was
confirmed. In practice, a larger value than 28 should be used
for the lock height for payment channels. Since 28 blocks had
already passed (meaning Bob techinically waited too late),
Alice can also create a transaction to actually obtain her old
(higher) balance of (almost) 0.6 bars as follows:

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"27d2263c2b7fa4dbeec021c4dd701ca87d420c863e1a2d14d2a5dbaf867dbead"}]' '[{"addr":"PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7","val":0.5997}]'

3b108091a5bf86535c03931a01fb6462482b05b93e9136e159f923dd76070e21ee86e340ed136230f4d168a1902edd7e35ecf36d15cd9900b22c4573780f71d373508aeb6e8f9d011400000068b0efa30404
```

```
signtx 3b108091a5bf86535c03931a01fb6462482b05b93e9136e159f923dd76070e21ee86e340ed136230f4d168a1902edd7e35ecf36d15cd9900b22c4573780f71d373508aeb6e8f9d011400000068b0efa30404 '["<AlicePrivKey>"]' '["6382012088a820e24e95259c70f35ff9e45e55173cfcde5f8636ad8af242bd01a2f87e19543cad8876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c3667041c000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e9136e159f923dd76070e21ee86e340ed136230f4d168a1902edd7e35ecf36d15cd9900b22c4573780f71d373508aeb6e8f9d011400000068b0efa304b40605a8b4f948e51b8f8f8ebdfff55b9d6c2db7dc98f228d6b286110a17ee726fe4a9aa477e853c57e8429b7bb5865fe97362caad9e63367dbd556eddc959550f9eeedb2056e6d493d3f41b52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff33640a661c70a0e0812316a90e29d562ec919eefcaff9c97bad7a91277fef5f0ddb6cad58bed0de0145e3f79b912acfd688eda6a6e8daa2d7f9356d9affb9b5654bb55cb7ab77789e244f9b670972040810a0ecba765353d43c3320d9ac8acdc3f728def479d014af77f7b873204ab4885901

sendtx 3b108091a5bf86535c03931a01fb6462482b05b93e9136e159f923dd76070e21ee86e340ed136230f4d168a1902edd7e35ecf36d15cd9900b22c4573780f71d373508aeb6e8f9d011400000068b0efa304b40605a8b4f948e51b8f8f8ebdfff55b9d6c2db7dc98f228d6b286110a17ee726fe4a9aa477e853c57e8429b7bb5865fe97362caad9e63367dbd556eddc959550f9eeedb2056e6d493d3f41b52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff33640a661c70a0e0812316a90e29d562ec919eefcaff9c97bad7a91277fef5f0ddb6cad58bed0de0145e3f79b912acfd688eda6a6e8daa2d7f9356d9affb9b5654bb55cb7ab77789e244f9b670972040810a0ecba765353d43c3320d9ac8acdc3f728def479d014af77f7b873204ab4885901

sendtx 3b108091a5bf86535c03931a01fb6462482b05b93e9136e159f923dd76070e21ee86e340ed136230f4d168a1902edd7e35ecf36d15cd9900b22c4573780f71d373508aeb6e8f9d011400000068b0efa304b40605a8b4f948e51b8f8f8ebdfff55b9d6c2db7dc98f228d6b286110a17ee726fe4a9aa477e853c57e8429b7bb5865fe97362caad9e63367dbd556eddc959550f9eeedb2056e6d493d3f41b52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff33640a661c70a0e0812316a90e29d562ec919eefcaff9c97bad7a91277fef5f0ddb6cad58bed0de0145e3f79b912acfd688eda6a6e8daa2d7f9356d9affb9b5654bb55cb7ab77789e244f9b670972040810a0ecba765353d43c3320d9ac8acdc3f728def479d014af77f7b873204ab4885901

b29e7599396b64e54f74390f56a7f90602a74b334d670cba534727e87adab220
```

Since Bob and Alice's txs both spend the asset
with id 27d2263c2b7fa4dbeec021c4dd701ca87d420c863e1a2d14d2a5dbaf867dbead
only one of them can be confirmed. If Bob had acted
faster than the 28 block locktime, then only Bob's transaction
would be valid until the 28 block locktime had passed.
In this case Bob's transaction happened to confirm
in Block 40270, so that Bob was indeed able to punish
Alice for trying to use an outdated commitment tx.

# Payment Channels with Proofs

Unlike Bitcoin, Proofgold has a script op, OP_PROVEN, that
can tell if a certain proposition has been proven.
Above the current pair of commitment txs for a payment channel
had precisely two outputs: one paying Alice her current balance
and another paying Bob his current balance. One of these outputs
would be controlled by an htlc address so that a party forfeits
their balance if they use an outdated commitment tx.
We now describe how commitment txs can contain a third output
(or generally multiple outputs beyond the first two) that
allow Alice and Bob to "bet" on whether or not a certain
proposition will be proven by a certain time.

The two parties begin by creating a channel with a third fund asset.

```
createchannel3 0252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb7 02a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc7 6d51ea519fc90fd4f273529dc591806f6cdb5fa0162bc7d93d83ad57a7702fc7 9e3a0aa96c11c813c25596d2d5bb450f950274d6a06fee3523bb0f6c9b434b1c 9.5 0.5

Funding tx: d19c0920cb523487f710373d07a5b8eef6d81940698b528ffa4c7ea0969f93ea2c8e047c63dbfe02b55839ceee196cbd3a857b398eab85d77c8d8df9cf564b8b1ad7b6bac339098f8da78e422a5b04f2847095a574f56ed143a5009d35e89b7bcdc8ee03dbe6d012871d08c0c8d25fc329ae81498d807d3231a495825c03000040374c1a27c00e046064e9afe114d7c0a446c03e9918d24a41ae010000608174870e60070230b2f4d7708a6b605223609f4c0c69a520d7000000000000000010cd9900b22c4573780f71d373508aeb6e8f9d0114000000581855380288ab85d77c8d8df9cf564b8b1ad7b6bac339098f0d0000002c84666b0000
Fund 2-of-2 address: PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL
Redeem script: 52210252641ed8d128f6c83931b852e2875ff1b9ecf4169b60572dbbe6dfb048fc3bb72102a18fbfada8ba24e41cf15cf0940d176319d7929eccf7ff587d007165a271edc752ae
Fund asset id 1: c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284
Fund asset id 2: ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56
Fund asset id 3: 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd
```

Alice begins by creating her first htlc.
This time we will use a locktime of 50 blocks instead of 28.

```
createhtlc PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 50

P2sh address: PsFDYfqeiZXe29gAoNZh2zEicZkGWzDjfsy
Redeem script: 6382012088a8202cdfc5d839ee82115c187599fdee4651b21ca5c59d5676af3efcf32c09e82d668876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c36670432000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac
Secret: 7e5c4910874e226a549ff10cf8cafda2597241154b8862310cd27f056476b038
Hash of secret: 2cdfc5d839ee82115c187599fdee4651b21ca5c59d5676af3efcf32c09e82d66
```

Alice creates her first commitment tx as before,
but spending the three fund assets instead of just two.
There are still only two outputs.

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":9.4999,"lockheight":0,"lockaddr":"PsFDYfqeiZXe29gAoNZh2zEicZkGWzDjfsy"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.4999,"lockheight":0,"lockaddr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2"}]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a01adfb5f28c95f1411feb9ccdd3d813520cd787d0000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000b0302ada0d08
```

Alice sends this to Bob along with the hash of the secret.
Bob verifies it as follows.

```
verifycommitmenttx3_2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 9.4999 0.4999 2cdfc5d839ee82115c187599fdee4651b21ca5c59d5676af3efcf32c09e82d66 50 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a01adfb5f28c95f1411feb9ccdd3d813520cd787d0000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000b0302ada0d08

Valid commitment tx for PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7
```

Bob signs Alice's commitment tx and sends the partially signed tx
to Alice.

```
simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a01adfb5f28c95f1411feb9ccdd3d813520cd787d0000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000b0302ada0d08 '["<BobPrivKey>"]' '["6382012088a8202cdfc5d839ee82115c187599fdee4651b21ca5c59d5676af3efcf32c09e82d668876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c36670432000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a01adfb5f28c95f1411feb9ccdd3d813520cd787d0000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000b0302ada0d680d0a10794f9fed7dc69e48d32a4ed4bce15b449cdd7c48ef58d117071abb2a68a4e7a5cb9f8890666fbf29d73af7dd567b44ded9034bb40970b2d7c1bb71e63e5ade3b479a20bf1f3e1cfea8d49002a592f5883d3a4afbc873c6c42d55fce1aff173b3a76f7133d8ab2d779bff0e1b29ff9db7430a0cfdf8776bd4ba4992e7189f2b7cca0d2f8ecd785db267e6f7ff63ed0b306e59d171db1f97eaea7000
```

Alice verifies the partially commitment tx and ensures her signature
is the only remaining requirement.

```
verifycommitmenttx3_2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 9.4999 0.4999 2cdfc5d839ee82115c187599fdee4651b21ca5c59d5676af3efcf32c09e82d66 50 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a01adfb5f28c95f1411feb9ccdd3d813520cd787d0000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000b0302ada0d680d0a10794f9fed7dc69e48d32a4ed4bce15b449cdd7c48ef58d117071abb2a68a4e7a5cb9f8890666fbf29d73af7dd567b44ded9034bb40970b2d7c1bb71e63e5ade3b479a20bf1f3e1cfea8d49002a592f5883d3a4afbc873c6c42d55fce1aff173b3a76f7133d8ab2d779bff0e1b29ff9db7430a0cfdf8776bd4ba4992e7189f2b7cca0d2f8ecd785db267e6f7ff63ed0b306e59d171db1f97eaea7000

Valid commitment tx for PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7

simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a01adfb5f28c95f1411feb9ccdd3d813520cd787d0000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000b0302ada0d680d0a10794f9fed7dc69e48d32a4ed4bce15b449cdd7c48ef58d117071abb2a68a4e7a5cb9f8890666fbf29d73af7dd567b44ded9034bb40970b2d7c1bb71e63e5ade3b479a20bf1f3e1cfea8d49002a592f5883d3a4afbc873c6c42d55fce1aff173b3a76f7133d8ab2d779bff0e1b29ff9db7430a0cfdf8776bd4ba4992e7189f2b7cca0d2f8ecd785db267e6f7ff63ed0b306e59d171db1f97eaea7000 '["<AlicePrivKey>"]' '["6382012088a8202cdfc5d839ee82115c187599fdee4651b21ca5c59d5676af3efcf32c09e82d668876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c36670432000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a01adfb5f28c95f1411feb9ccdd3d813520cd787d0000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000b0302ada0d680d0a307defdab3d532c40b7fa465e9be43339e2f5a7bc9eb02e9574cba143bd3c120b7fb17ce5d72d19c763d42dd1fb4fcfdddeecbaa1e4c3064edeb31cbd38cce9c6869fdc9c1c306af3b2840e43d7db6f7197b224dab3851f3866f117176f321bd63455f1c68ecaaa0919e972e7f22429abdfda65cebdc775bed1179670f2cd126c0c95e07efc699fb6879ef1c6982fc7ef870f8a352430a944ad623f6e828ed23cf1913b754f187bfc6cfcd9ebec5cd60afb6dc6dfe3b6ca4fc77de0e2930f4e3dfad51eb26499e637caef02937bc3836e375c99e99dfff8fb52fc0b86545c76d7f5caaab3528c0c2246fc3160912ac5c888f05220f5ff5f1e6fbfe7ffaeefe53e4d3d51ee54f873e18377a9890351b665df8e6dfbc347b72550d79fc7196016f43ffb95da5ebbde035528458d2b2daa00091f7f4d9de67ec8934ade244cd1bbe45c4d9cd87f48e157d71a0b1ab82467a5ebafc890869f6f69b72ad73df6db547e49d3db0449b00277b1dbc1b67eea3e5bd73a409f2fbe1c3e18f4a0d29502a598fd8a3a3b48f3c674cdc52c51ffe1a3f377bfa163783bdda72b7f9efb091f2df793ba4c0d08f7fb746ad9b24798ef1b9c2a7dcf0e2d88cd7257b667eff3fd6be00e396151db7fd71a9aed6a000034ff40bf3beeeadadbbe3ecea50797fc3ddcf3bcf385476e9d4eb79ff1d9e153f75ac2cf326944b77e2e3cb73057b16ea99f564a3f9af3a6c5fd3274d929c1737ef2c55e351ac59830244ded3677b9fb127d2b48a13356ff8161167371fd23b56f4c581c6ae0a1ae979e9f22722a4d9db6fcab5ce7db7d51e9177f6c0126d029cec75f06e9cb98f96f7ce9126c8ef870f873f2a35a440a9643d628f8ed23ef29c31714b157ff86bfcdcece95bdc0cf66acbdde6bfc346ca7fe7ed9002433ffedd1ab56e92e439c6e70a9f72c38b63335e97ec99f9fdff58fb028c5b5674dcf6c7a5ba02
Completely signed.
```

Reversing the roles of Alice and Bob, Bob creates an initial commitment tx.

```
createhtlc PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 50

P2sh address: PsTYuTmwTXvurwCDpeAGbP6smoaAA5QFcHU
Redeem script: 6382012088a8203688455c8145cf45ac5ee293f6ad9eefad5125b06d8da8976ba5901d71178e938876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac
Secret: 903fc1d134a0c5b25dd60db07eb9d8662103255de7473af417ebfa2f8daefcb9
Hash of secret: 3688455c8145cf45ac5ee293f6ad9eefad5125b06d8da8976ba5901d71178e93

createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":9.4999,"lockheight":0,"lockaddr":"PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.4999,"lockheight":0,"lockaddr":"PsTYuTmwTXvurwCDpeAGbP6smoaAA5QFcHU"}]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c8f589a5bc9a5683acf7f8dcaeb33435c4b734f2f8590000000000000000000000b0302ada0d08
```

Alice verifies the commitment tx and signs it.

```
verifycommitmenttx3_2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 9.4999 0.4999 3688455c8145cf45ac5ee293f6ad9eefad5125b06d8da8976ba5901d71178e93 50 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c8f589a5bc9a5683acf7f8dcaeb33435c4b734f2f8590000000000000000000000b0302ada0d08

Valid commitment tx for PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2

simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c8f589a5bc9a5683acf7f8dcaeb33435c4b734f2f8590000000000000000000000b0302ada0d08 '["<AlicePrivKey>"]' '["6382012088a8203688455c8145cf45ac5ee293f6ad9eefad5125b06d8da8976ba5901d71178e938876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c8f589a5bc9a5683acf7f8dcaeb33435c4b734f2f8590000000000000000000000b0302ada0d680d0ab06ee9ea64df43ec1efc3262b3d813763e8c99bd4cde1a35e70ed95a76daaee8290bb4de50ed44b4dd8dc77eaa34f4d1edc6474fc71fdf6c78edc4714e6f0bf9f7f8fd254fefec29fba8d49002a592f5883d3a4afbc873c6c42d55fce1aff173b3a76f7133d8ab2d779bff0e1b29ff9db7430a0cfdf8776bd4ba4992e7189f2b7cca0d2f8ecd785db267e6f7ff63ed0b306e59d171db1f97eaea7000
```

Alice gives the partially signed commitment tx to Bob.
Bob verifies it and ensures his signature is the only remaining requirement.

```
verifycommitmenttx3_2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 9.4999 0.4999 3688455c8145cf45ac5ee293f6ad9eefad5125b06d8da8976ba5901d71178e93 50 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c8f589a5bc9a5683acf7f8dcaeb33435c4b734f2f8590000000000000000000000b0302ada0d680d0ab06ee9ea64df43ec1efc3262b3d813763e8c99bd4cde1a35e70ed95a76daaee8290bb4de50ed44b4dd8dc77eaa34f4d1edc6474fc71fdf6c78edc4714e6f0bf9f7f8fd254fefec29fba8d49002a592f5883d3a4afbc873c6c42d55fce1aff173b3a76f7133d8ab2d779bff0e1b29ff9db7430a0cfdf8776bd4ba4992e7189f2b7cca0d2f8ecd785db267e6f7ff63ed0b306e59d171db1f97eaea7000

Valid commitment tx for PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2

simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c8f589a5bc9a5683acf7f8dcaeb33435c4b734f2f8590000000000000000000000b0302ada0d680d0ab06ee9ea64df43ec1efc3262b3d813763e8c99bd4cde1a35e70ed95a76daaee8290bb4de50ed44b4dd8dc77eaa34f4d1edc6474fc71fdf6c78edc4714e6f0bf9f7f8fd254fefec29fba8d49002a592f5883d3a4afbc873c6c42d55fce1aff173b3a76f7133d8ab2d779bff0e1b29ff9db7430a0cfdf8776bd4ba4992e7189f2b7cca0d2f8ecd785db267e6f7ff63ed0b306e59d171db1f97eaea7000 '["<BobPrivKey>"]' '["6382012088a8203688455c8145cf45ac5ee293f6ad9eefad5125b06d8da8976ba5901d71178e938876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000e87e892e00dc81008c2cfd359ce21a98d408d82713435a29c8f589a5bc9a5683acf7f8dcaeb33435c4b734f2f8590000000000000000000000b0302ada0d680d0ab06ee9ea64df43ec1efc3262b3d813763e8c99bd4cde1a35e70ed95a76daaee8290bb4de50ed44b4dd8dc77eaa34f4d1edc6474fc71fdf6c78edc4714e6f0bf9f7f8fd254fefec293b28409031a12f7ccb52f4e7f2f38f1a3fdf5576fc8ef7c10655ffbb24e2b9b2e5c25f5e1a7ad89ed817d337dc7cf4cef424c52b5e08d27f78db1a892ac62efca8cfb7bd251606889fffd7a352430a944ad623f6e828ed23cf1913b754f187bfc6cfcd9ebec5cd60afb6dc6dfe3b6ca4fc77de0e2930f4e3dfad51eb26499e637caef02937bc3836e375c99e99dfff8fb52fc0b86545c76d7f5caaab3528c0baa5ab937d0fb17bf0cb88cd624fd8f93066f632796bd49c3b646bd969bba2a72cd07a43b513d176371efba9d2d047b71b1f3d1d7f7cb3e1b513c739bd2de4dfe3f7973cbdb3a7eca000f7cb4efd94fa4bfcff23460f483ce7f1c997eb13af989a30f4ec36f1f25cfc98e7f493e2b9e28dbef163cbd3c677cafdda7b6fe7a05cbd77961a7274e3aa798d4ae66af06b77a74b8f4a0d29502a598fd8a3a3b48f3c674cdc52c51ffe1a3f377bfa163783bdda72b7f9efb091f2df793ba4c0d08f7fb746ad9b24798ef1b9c2a7dcf0e2d88cd7257b667eff3fd6be00e396151db7fd71a9aed6a000eb96ae4ef63dc4eec12f23368b3d61e7c398d9cbe4ad5173ee90ad65a7ed8a9eb240eb0dd54e44dbdd78eca74a431fdd6e7cf474fcf1cd86d74e1ce7f4b6907f8fdf5ff2f4ce9eb283024c5952e45893920716740f9d74e29ed807e37c9f976e72f81b659a8c899a3b66be23079e7e69b9e64ecd6577b3a57ff4356bab06b3478cff5f624fc44f798705ff533fd2e48aabe73e2a35a440a9643d628f8ed23ef29c31714b157ff86bfcdcece95bdc0cf66acbdde6bfc346ca7fe7ed9002433ffedd1ab56e92e439c6e70a9f72c38b63335e97ec99f9fdff58fb028c5b5674dcf6c7a5ba02
Completely signed.
```

Now Alice signs the funding tx.

```
signtx d19c0920cb523487f710373d07a5b8eef6d81940698b528ffa4c7ea0969f93ea2c8e047c63dbfe02b55839ceee196cbd3a857b398eab85d77c8d8df9cf564b8b1ad7b6bac339098f8da78e422a5b04f2847095a574f56ed143a5009d35e89b7bcdc8ee03dbe6d012871d08c0c8d25fc329ae81498d807d3231a495825c03000040374c1a27c00e046064e9afe114d7c0a446c03e9918d24a41ae010000608174870e60070230b2f4d7708a6b605223609f4c0c69a520d7000000000000000010cd9900b22c4573780f71d373508aeb6e8f9d0114000000581855380288ab85d77c8d8df9cf564b8b1ad7b6bac339098f0d0000002c84666b0000

d19c0920cb523487f710373d07a5b8eef6d81940698b528ffa4c7ea0969f93ea2c8e047c63dbfe02b55839ceee196cbd3a857b398eab85d77c8d8df9cf564b8b1ad7b6bac339098f8da78e422a5b04f2847095a574f56ed143a5009d35e89b7bcdc8ee03dbe6d012871d08c0c8d25fc329ae81498d807d3231a495825c03000040374c1a27c00e046064e9afe114d7c0a446c03e9918d24a41ae010000608174870e60070230b2f4d7708a6b605223609f4c0c69a520d7000000000000000010cd9900b22c4573780f71d373508aeb6e8f9d0114000000581855380288ab85d77c8d8df9cf564b8b1ad7b6bac339098f0d0000002c84666b00186f77f89160bfcd775baec0362de8d973e3bf0ec5a570637290ed51a2b13dc8a48cae2d94c82c347398637e2624b083359ef2773d26fd9f5b1627c05997e866261bb49d2a6aca1900f753fc6479da9586888ccf0be66643b6e6e96ac7f2859a71274f20deea47b3c33208d158a4c45d28e73af73fff464cf4f011b1106bfc2e3704
Partially signed.
```

Then Bob signs the funding tx and sends it, opening the channel.

```
signtx d19c0920cb523487f710373d07a5b8eef6d81940698b528ffa4c7ea0969f93ea2c8e047c63dbfe02b55839ceee196cbd3a857b398eab85d77c8d8df9cf564b8b1ad7b6bac339098f8da78e422a5b04f2847095a574f56ed143a5009d35e89b7bcdc8ee03dbe6d012871d08c0c8d25fc329ae81498d807d3231a495825c03000040374c1a27c00e046064e9afe114d7c0a446c03e9918d24a41ae010000608174870e60070230b2f4d7708a6b605223609f4c0c69a520d7000000000000000010cd9900b22c4573780f71d373508aeb6e8f9d0114000000581855380288ab85d77c8d8df9cf564b8b1ad7b6bac339098f0d0000002c84666b00186f77f89160bfcd775baec0362de8d973e3bf0ec5a570637290ed51a2b13dc8a48cae2d94c82c347398637e2624b083359ef2773d26fd9f5b1627c05997e866261bb49d2a6aca1900f753fc6479da9586888ccf0be66643b6e6e96ac7f2859a71274f20deea47b3c33208d158a4c45d28e73af73fff464cf4f011b1106bfc2e3704

d19c0920cb523487f710373d07a5b8eef6d81940698b528ffa4c7ea0969f93ea2c8e047c63dbfe02b55839ceee196cbd3a857b398eab85d77c8d8df9cf564b8b1ad7b6bac339098f8da78e422a5b04f2847095a574f56ed143a5009d35e89b7bcdc8ee03dbe6d012871d08c0c8d25fc329ae81498d807d3231a495825c03000040374c1a27c00e046064e9afe114d7c0a446c03e9918d24a41ae010000608174870e60070230b2f4d7708a6b605223609f4c0c69a520d7000000000000000010cd9900b22c4573780f71d373508aeb6e8f9d0114000000581855380288ab85d77c8d8df9cf564b8b1ad7b6bac339098f0d0000002c84666b00186f77f89160bfcd775baec0362de8d973e3bf0ec5a570637290ed51a2b13dc8a48cae2d94c82c347398637e2624b083359ef2773d26fd9f5b1627c05997e866261bb49d2a6aca1900f753fc6479da9586888ccf0be66643b6e6e96ac7f2859a71274f20deea47b3c33208d158a4c45d28e73af73fff464cf4f011b1106bfc2e378cc7ed71a26571007d58fff7cc9e92d71963170d94f05cf11ce424baa8adbf8fa1aaa1ee6c1b08201e531f1bfe9d1b17a96ba26150096e9f8488ee0aeb6a0bc838a7ddf82dc4b007fa3cbf81e3806f60aee265547d423196d147d6f340c913252df8cd6fe28f272af5e22586c4f4d11d71b20984e19d85693c833087b5f9816c1800
Completely signed.

sendtx d19c0920cb523487f710373d07a5b8eef6d81940698b528ffa4c7ea0969f93ea2c8e047c63dbfe02b55839ceee196cbd3a857b398eab85d77c8d8df9cf564b8b1ad7b6bac339098f8da78e422a5b04f2847095a574f56ed143a5009d35e89b7bcdc8ee03dbe6d012871d08c0c8d25fc329ae81498d807d3231a495825c03000040374c1a27c00e046064e9afe114d7c0a446c03e9918d24a41ae010000608174870e60070230b2f4d7708a6b605223609f4c0c69a520d7000000000000000010cd9900b22c4573780f71d373508aeb6e8f9d0114000000581855380288ab85d77c8d8df9cf564b8b1ad7b6bac339098f0d0000002c84666b00186f77f89160bfcd775baec0362de8d973e3bf0ec5a570637290ed51a2b13dc8a48cae2d94c82c347398637e2624b083359ef2773d26fd9f5b1627c05997e866261bb49d2a6aca1900f753fc6479da9586888ccf0be66643b6e6e96ac7f2859a71274f20deea47b3c33208d158a4c45d28e73af73fff464cf4f011b1106bfc2e378cc7ed71a26571007d58fff7cc9e92d71963170d94f05cf11ce424baa8adbf8fa1aaa1ee6c1b08201e531f1bfe9d1b17a96ba26150096e9f8488ee0aeb6a0bc838a7ddf82dc4b007fa3cbf81e3806f60aee265547d423196d147d6f340c913252df8cd6fe28f272af5e22586c4f4d11d71b20984e19d85693c833087b5f9816c1800

15ff7c60de6686372170e7cf796291b0bfaab122b07614e27efe5e8ab037d7f8
```

This tx confirmed in Block 40329, opening this payment channel.
Suppose the current block has height 40450.  Now suppose Alice wants a
proof the classical principle Peirce's Law in the (classical) HOTG
theory.  A document with Peirce's Law in Proofgold document format
looks as follows:

```
Document 29c988c5e6c620410ef4e61bcfcbe4213c77013974af40759d8b732c07d61967
Conj PeirceLaw : All p Prop All q Prop Imp Imp Imp p q p p
```

Using `readdraft` on this document, the propid of Peirce's Law
is revealed to be
6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752
and the corresponding address of Peirce's Law
is revealed to be TMHdiB3JuSACro7AR3Q9TpunvWDNtsMCW81.
Using `query` on this address we see the address is empty, and
hence unproven at the moment.

Suppose Bob believes he can supply a proof of Peirce's Law
within a day or so.

Alice can *bet* Bob 5 Proofgold bars at 100:1 odds that there will
*not* be a proof of Peirce's Law in the HOTG theory by Block 40550 (a
block that should be reached in about 2 days). She does this because
she actually wants there to be a proof and is willing to pay for one.
Bob bets there *will* be a proof of Peirce's Law before Block 40550.
To take the other side of the bet, Bob must contribute 0.05 Proofgold bars.

This bet can be realized offchain using the payment channel
by creating new commitment transactions with three outputs.
The first two outputs are as before, reflecting the balances of Alice and Bob.
The third output should go to Alice if there is no proof of Peirce's Law
(by Block 40550) and should go to Bob if there is a proof of Peirce's Law
(by Block 40550).

A first attempt to create a script to control the third output
is by using a *prop timelock contract* script.
The command `createptlc` can be used to
create such a script (and corresponding address).
In this case, it could be done as follows:

```
createptlc PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 40550 absolute

P2sh address: PsYk1Bq2M9svuLbfCCB6Ko5GaxGg2SwFDtE
Redeem script: 63206fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752b57576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366704669e0000b17576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac
Propid: 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752
```

Note that there is no *secret* here, so both Alice and Bob can call
the command `createptlc` as above and agree on the script and p2sh
address.  Now Alice and Bob could create new commitment transactions
reflecting Alice's new balance of 4.5 bars, Bob's new balance of 0.45
bars, and the third balance of 5.05 bars controlled by the ptlc p2sh
address PsYk1Bq2M9svuLbfCCB6Ko5GaxGg2SwFDtE.  (Technically, each value
would be slightly less to account for tx fees.)  If Alice or Bob were
to close the channel with one of the commitment txs, then Alice would
be able to spend the third output after Block 40550 but Bob would be
able to spend the third output immediately if a proof of Peirce's Law
has been confirmed in a Proofgold block.  In practice, Bob could
simply send Alice the proof of Peirce's Law (offchain), and then Alice
and Bob could update the channel by creating new commitment txs (with
2 outputs) reflecting a balance of 4.5 bars for Alice and a balance of
5.5 bars for Bob. If Alice did not cooperate by creating the new
commitment txs, then Bob could publish the current commitment tx,
publish the proof of Peirce's Law (onchain) and collect the third
output immediately, as well as the second output (the htlc output)
after 50 confirmations.

A slight problem now arises. Suppose Bob has proven Peirce's law,
given that proof to Alice and Alice and Bob have updated the balances.
We now have three pairs of commitment txs, the first two of which are
outdated. We know why neither Alice nor Bob will publish one of the
old commitment txs, since the htlc scripts controlling the first two
outputs will allow the other party to use the revealed secret to spend
both of the first two outputs. However, this does not apply to the
third output, controlled by a ptlc script.  Suppose the channel
remains open past Block 40550.  Alice could publish the outdated
second tx and immediately spend the third output, before Bob has a
chance to publish the proof of Peirce's Law on chain. Bob could punish
Alice by spending the first two txs, but this would result in Alice
obtaining 5.05 bars and Bob obtaining 4.95 bars. This is less than
Bob's supposed balance of 5.5 bars, and more than Alice's supposed
balance of 4.5 bars.  Likewise, if Alice and Bob continued to update
the channel over time, after Block 40550 either of them could go back
to the second commitment tx, sacrificing their primary balance, and
collecting the third output. This is always possible for Alice, but
also possible for Bob -- even before Block 40550 -- if Bob publishes
the proof of Peirce's Law onchain.

This makes it clear that we need an htlc-like behavior in combination
with the ptlc-like behavior. That is, the script should be htlc-like
in the sense that after a secret is revealed, the offending party can
immediately spend the third output, but without the secret (after,
say, 50 blocks) the behavior is like the ptlc script above.  Note that
once this modification is made, Bob will need to publish the
commitment tx before Block 40500 and then publish the proof of
Peirce's Law onchain before Block 40550 in order to spend the third
output before Alice is allowed to spend it instead.
In effect, Bob is now betting there will be a proof by Block 40500,
not Block 40550. On the other hand, Alice is betting there will
not be a proof by Block 40550. Technically, if Bob produces a proof
and publishes it on chain between Blocks 40500 and 40550,
either party could be considered the winner of the bet.
In that case, note that Alice does obtain the desired proof.

The command `createhtlcptlc` can be used to create such a script and
corresponding address. As before, both Alice and Bob use the command
(with different arguments) to create appropriate scripts for their new
commitment transactions. The first argument should be the other
party's address, as they should be able to immediately spend the
output using the secret if the commitment tx is ever revoked. The
second argument should be the party who is betting there will be a
proof (in this case, Bob's address) while the second argument should
be the party who is betting there will not be a proof (in this case,
Alice's address). Note that this means when Alice is calling
`createhtlcptlc`, the first three arguments will be *BobAddress*,
*BobAddress* and *AliceAddress*.  When Bob is calling
`createhtlcptlc`, the first three arguments will be *AliceAddress*,
*BobAddress* and *AliceAddress*.  The fourth argument is the timelock
corresponding to the htlc behavior. This is (with the current
implementation) always a relative (CSV) timelock, and in this example
we have chosen 50 blocks for commitment txs.  The fifth argument is
the timelock corresponding to the ptlc behavior. This is (with the
current implementation) always an absolute (CLTV) timelock. We have
chosen 40550 as the block height for th CLTV timelock in this example.
The sixth argument is the propid for the conjecture.  For Peirce's Law
this is
6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752.  One
can optionally give a 64-hex secret to use for the htlc behavior, or
omit it to allow the software to generate a secret.  One can also
optionally give the keyword `json` as a final argument if the output
should be in json format.

Alice calls `createhtlcptlc` as follows:

```
createhtlcptlc PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 50 40550 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752

P2sh address: PsTgNt6n8rs1S5kFftxraM5QbLQmPkoGdif
Redeem script: 6382012088a820d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb458876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c36670432000000b27563206fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752b57576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366704669e0000b17576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328686888ac
Secret: 6451d568e075651a0c5c5f8dc4565b7764bf2c9765b773c8476cd528a5355ae8
Hash of secret: d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb45
```

Alice still needs to also create an htlc address
for the first output of the new commitment tx.
The secret may be the same as the secret for the htlcptlc address,
or may be different. If different, both secrets need to be kept
secret unless the commitment is revoked in the future -- in which
case both secrets must be shared. For simplicity, we use the same
secret.

```
createhtlc PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 50 6451d568e075651a0c5c5f8dc4565b7764bf2c9765b773c8476cd528a5355ae8

P2sh address: PsPHzE2L8PXJKbzVPbZe6RzJzgZMVQymuzH
Redeem script: 6382012088a820d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb458876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c36670432000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac
Secret: 6451d568e075651a0c5c5f8dc4565b7764bf2c9765b773c8476cd528a5355ae8
Hash of secret: d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb45
```

Alice now creates her new commitment tx
reflecting Alice's new balance of 4.5 bars,
Bob's new balance of 0.45 bars
and the bet balance of 5.05 bars.

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":4.4999,"lockheight":0,"lockaddr":"PsPHzE2L8PXJKbzVPbZe6RzJzgZMVQymuzH"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.4499,"lockheight":0,"lockaddr":"PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":5.0499,"lockheight":0,"lockaddr":"PsTgNt6n8rs1S5kFftxraM5QbLQmPkoGdif"}]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a2d797c2aa03c3bac73cfbab0928a9999c9c72c360000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290eb171f12f536ce265dd3e51f8954df526605a64a1a0000000000000000000000a06ef2771c10
```

Alice shares this unsigned commitment tx with Bob as well
as the hash of the secret (or both secrets, if two secrets were used).
Bob can verify the commitment tx as follows:

```
verifycommitmenttx3_3 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 4.4999 0.4499 5.0499 50 40550 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb45 d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb45 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a2d797c2aa03c3bac73cfbab0928a9999c9c72c360000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290eb171f12f536ce265dd3e51f8954df526605a64a1a0000000000000000000000a06ef2771c10

Valid commitment tx for PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 with counterparty PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2
where PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 bets 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 will be proven by the deadline
and PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 bets it will not be.
```

Bob then signs this tx and gives the signed tx to Alice.

```
simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a2d797c2aa03c3bac73cfbab0928a9999c9c72c360000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290eb171f12f536ce265dd3e51f8954df526605a64a1a0000000000000000000000a06ef2771c10 '["<BobPrivKey>"]' '["6382012088a820d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb458876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c36670432000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a2d797c2aa03c3bac73cfbab0928a9999c9c72c360000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290eb171f12f536ce265dd3e51f8954df526605a64a1a0000000000000000000000a06ef2771cd01a14e06aba2ab51f4c7e7a24789d04738374f956e4d9c1d3d5c65edf192de8bce369a60daf743b4cb3d799a2e41d3a6eebae8775066f2b55f4c392d5a70304ccdcfe6a8d93259246ca55ea51a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed5d5e100
```

Alice should take this partially signed tx and verify it
is still a valid commitment tx for her (i.e., that Bob did not
send her some other partially signed tx) and that her signature
is all that is needed to complete the signatures for the tx.

```
verifycommitmenttx3_3 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 4.4999 0.4499 5.0499 50 40550 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb45 d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb45 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a2d797c2aa03c3bac73cfbab0928a9999c9c72c360000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290eb171f12f536ce265dd3e51f8954df526605a64a1a0000000000000000000000a06ef2771cd01a14e06aba2ab51f4c7e7a24789d04738374f956e4d9c1d3d5c65edf192de8bce369a60daf743b4cb3d799a2e41d3a6eebae8775066f2b55f4c392d5a70304ccdcfe6a8d93259246ca55ea51a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed5d5e100

Valid commitment tx for PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 with counterparty PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2
where PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 bets 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 will be proven by the deadline
and PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 bets it will not be.

simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a2d797c2aa03c3bac73cfbab0928a9999c9c72c360000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290eb171f12f536ce265dd3e51f8954df526605a64a1a0000000000000000000000a06ef2771cd01a14e06aba2ab51f4c7e7a24789d04738374f956e4d9c1d3d5c65edf192de8bce369a60daf743b4cb3d799a2e41d3a6eebae8775066f2b55f4c392d5a70304ccdcfe6a8d93259246ca55ea51a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed5d5e100 '["<AlicePrivKey>"]' '["6382012088a820d34471f4e9d7d52b88a3dd3cdc952e983e8d0e07ed52eb633d3dfb24d89dbb458876a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c36670432000000b27576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b03286888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e47a2d797c2aa03c3bac73cfbab0928a9999c9c72c360000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c875ae165ef33536e63f5b2d2d6a5cdbea0ee7243c360000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290eb171f12f536ce265dd3e51f8954df526605a64a1a0000000000000000000000a06ef2771cd01a14a0e3ee8c1bebad4abd2c6bf239517becfcf1bde68552955357799e3d5b93a24742dcad1a71cfa3d80587d4397daf73d0206beb5ca9d9ff5f96dbcb77bd3b99f9d5e441bf6b265ad56d5080abe9aad47e30f9e991e07512cc0dd2e55b9167074f571b7b7d67b4a0f38ea79936bcd2ed30cd5e678a9277e8b8adbb1ed619bcad54d10f4b569f0e103073fbab354e96481a2957a947a586142895ac47ecd151da479e33266ea9e20f7f8d9f9b3d7d8b9bc15e6db9dbfc77d848f9efbc1d5260e8c7bf5ba3d64d923cc7f85ce1536e78716cc6eb923d33bfff1f6b5f8071cb8a8edbfeb854576b5080155fdbc4e812f1dad6e3f15b9d9ef124fcccec1393559d116bc38f07ff23ef8f97a6e8ac93b3ba94fa79af72b998293287ae323a4addf6c18b470a58b8ccba2cc92a1f5eb4e1cbd34101aea6ab52fbc1e4a74782d749303748976f459e1d3c5d6decf59dd182ce3b9e66daf04ab7c3347b9d294adea1e3b6ee7a5867f0b652453f2c597d3a40c0ccedafd638592269a45ca51e951a52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff3764881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe3525dad4101ee2c1c963f5eab0b6f1e965adeb8f0e55923ff8f4b37295d9e7ba97ab78e31bfdf8e28d1871e3cb62df4d2d47fb7441b5d2b45e4049fbfedef18a860db74318e1c2ff97ed3c2db750705b89aae4aed07939f1e095e27c1dc205dbe157976f074b5b1d777460b3aef789a69c32bdd0ed3ec75a62879878edbbaeb619dc1db4a15fdb064f5e9000133b7bf5ae36489a49172957a546a488152c97ac41e1da57de43963e2962afef0d7f8b9d9d3b7b819ecd596bbcd7f878d94ffcedb2105867efcbb356add24c9738ccf153ee58617c766bc2ed933f3fbffb1f60518b7ace8b8ed8f4b7505

Completely signed.
```

Bob now creates his new commitment tx
reflecting the balances including the bet balance of 5.05 bars.

Bob calls `createhtlcptlc` as follows:

```
createhtlcptlc PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 50 40550 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752

P2sh address: PsPq93hcP1HshyZWtQYy5NaojFTaCdLeHiR
Redeem script: 6382012088a820fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27563206fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752b57576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366704669e0000b17576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328686888ac
Secret: cb1cb4c50830dfe780fa5e8682c7c4e70482a987c2530f4a2de4ab9e103bb5a1
Hash of secret: fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b
```

Bob also creates a new htlc address, and again we reuse
the secret generated by `createhtlcptlc`.

```
createhtlc PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 50 cb1cb4c50830dfe780fa5e8682c7c4e70482a987c2530f4a2de4ab9e103bb5a1

P2sh address: PsSALcRXS3swxQgzc5zbc9aK1ZUpBxQCr1x
Redeem script: 6382012088a820fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac
Secret: cb1cb4c50830dfe780fa5e8682c7c4e70482a987c2530f4a2de4ab9e103bb5a1
Hash of secret: fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b
```

Bob creates his new commitment tx, where the first output is Alice's balance,
the second output is Bob's balance controlled by the new htlc address,
and the third output is the bet balance controlled by the new htlcptlc address.

```
createtx '[{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56"},{"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL":"794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd"}]' '[{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":4.4999,"lockheight":0,"lockaddr":"PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":0.4499,"lockheight":0,"lockaddr":"PsSALcRXS3swxQgzc5zbc9aK1ZUpBxQCr1x"},{"addr":"PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL","val":5.0499,"lockheight":0,"lockaddr":"PsPq93hcP1HshyZWtQYy5NaojFTaCdLeHiR"}]'
3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c8f57a6909888d185e16bbb870b83446f689a53493920000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290ebc1ae754c15bb86a49abb93083ca3e299a68628d40000000000000000000000a06ef2771c10
```

Bob sends this unsigned tx to Alice along with the hash of the secret.
Alice verifies it is an appropriate commitment tx and then signs it,
sending the partially signed tx back to Bob.

```
verifycommitmenttx3_3 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 4.4999 0.4499 5.0499 50 40550 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c8f57a6909888d185e16bbb870b83446f689a53493920000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290ebc1ae754c15bb86a49abb93083ca3e299a68628d40000000000000000000000a06ef2771c10

Valid commitment tx for PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 with counterparty PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7
where PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 bets 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 will be proven by the deadline
and PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 bets it will not be.

simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c8f57a6909888d185e16bbb870b83446f689a53493920000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290ebc1ae754c15bb86a49abb93083ca3e299a68628d40000000000000000000000a06ef2771c10 '["<AlicePrivKey>"]' '["6382012088a820fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac","6382012088a820fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27563206fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752b57576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366704669e0000b17576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328686888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c8f57a6909888d185e16bbb870b83446f689a53493920000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290ebc1ae754c15bb86a49abb93083ca3e299a68628d40000000000000000000000a06ef2771cd01a14e04bb95c915fedaf7ea568bfd19d7fad5e717058aa91eb9744097fe77899b049965f8bfee7cec77209bf4729f4ab58ce70e9074de99cb852def3519ece4a52707dabdb01365668dff851a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed5d5e100
Partially signed.
```

Bob can verify the partially signed commitment tx 
and privately sign it to ensure that his signature is the only
remaining requirement.

```
verifycommitmenttx3_3 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 PsFe9hRkyap4SkbpkZ17EPa2yx5zASXVarL c76cd0bf691734550af99af0e4647481fb0c821645e7a27e1cc5bdbd09a26284 ee0b0d9169fa1747ee091763131dcce1e9792d3a9e36123b52bb558e8c124d56 794addbb4aed3e4a3692a95a0448dbba25a8e39e31021c0cc3ca6c24a69e49fd 4.4999 0.4499 5.0499 50 40550 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c8f57a6909888d185e16bbb870b83446f689a53493920000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290ebc1ae754c15bb86a49abb93083ca3e299a68628d40000000000000000000000a06ef2771cd01a14e04bb95c915fedaf7ea568bfd19d7fad5e717058aa91eb9744097fe77899b049965f8bfee7cec77209bf4729f4ab58ce70e9074de99cb852def3519ece4a52707dabdb01365668dff851a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed5d5e100

Valid commitment tx for PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 with counterparty PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7
where PrJrmmKDsVNS58tZXtqeNMR361LHegXEvT2 bets 6fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752 will be proven by the deadline
and PrH3cZ3LFW8k4Kg3ippQLsbsGYAmZrG5NX7 bets it will not be.

simplesigntx 3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c8f57a6909888d185e16bbb870b83446f689a53493920000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290ebc1ae754c15bb86a49abb93083ca3e299a68628d40000000000000000000000a06ef2771cd01a14e04bb95c915fedaf7ea568bfd19d7fad5e717058aa91eb9744097fe77899b049965f8bfee7cec77209bf4729f4ab58ce70e9074de99cb852def3519ece4a52707dabdb01365668dff851a921054a25eb117b7494f691e78c895baaf8c35fe3e7664fdfe266b0575bee36ff1d3652fe3b6f871418faf1efd6a8759324cf313e57f8941b5e1c9bf1ba64cfccefffc7da1760dcb2a2e3b63f2ed5d5e100 '["<BobPrivKey>"]' '["6382012088a820fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366888ac","6382012088a820fa4590a65575b7f9cb283adeab37deb8e8da38758fe665d0ae5dacb63af31b7b8876a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328670432000000b27563206fd4d87cc41bb68fe5c0761253936d4ff5350479f09e46989ed2558382ab6752b57576a914ae165ef33536e63f5b2d2d6a5cdbea0ee7243c366704669e0000b17576a9149a330164598ae6f01ee2a6e7a014d7dd1e3b0328686888ac"]'

3b108091a5bf86535c03931a01fb6462482b05b93e6683fe4dbba0a952c8d7842727a30bdc6710b4283a17f5e328eeed4d101523dc81008c2cfd359ce21a98d408d82713435a29c8b5fb4243649afec5917bc2c5d8440773787a5e8b8ea78dc48ed46e9523a34493d50e046064e9afe114d7c0a446c03e9918d24a41aef394ba7795da7d946c2453b50890b6754b50c73d630438188695d9484c3d93faed40004696fe1a4e710d4c6a04ec938921ad14e43acd9900b22c4573780f71d373508aeb6e8f9d01140000000000000000000000402bf6eb03dc81008c2cfd359ce21a98d408d82713435a29c8f57a6909888d185e16bbb870b83446f689a53493920000000000000000000000a090c7b90eb803011859fa6b38c53530a911b04f2686b45290ebc1ae754c15bb86a49abb93083ca3e299a68628d40000000000000000000000a06ef2771cd01a14e04bb95c915fedaf7ea568bfd19d7fad5e717058aa91eb9744097fe77899b049965f8bfee7cec77209bf4729f4ab58ce70e9074de99cb852def3519ece4a52707dabdb01365668df78508086b7b22f8fb2aa7e90a21bea85195baafdd8305f0ede6b927563ee62cbe66e7b97be6bb8cdf737cd6ff5614db51a2f2b576c37e267bd94778b8ce955b070e778d58f3eda1c66589c47a586142895ac47ecd151da479e33266ea9e20f7f8d9f9b3d7d8b9bc15e6db9dbfc77d848f9efbc1d5260e8c7bf5ba3d64d923cc7f85ce1536e78716cc6eb923d33bfff1f6b5f8071cb8a8edbfeb854576b50802fe572457eb5bffa95a2fd4677feb57ac5c161a946ae5f1225fc9de365c226597e2dfa9f3b1fcb25fc1ea5d0af6239c3a51f34a573e24a79cf47793a2b49c1f5ad6e07d858a17de3410156d65bfca9d7b9873dc2265f7fe4ea81f4d7c7e7af582c77b695b36265593936ebcf09b31a25acf07ec4d3050933cecab6b46af666a1ce45cfffb270c1f28793af2b1ae8c8dd3bb51f951a52a054b21eb14747691f79ce98b8a58a3ffc357e6ef6f42d6e067bb5e56ef3df6123e5bff3764881a11fff6e8d5a3749f21ce373854fb9e1c5b119af4bf6ccfcfe7fac7d01c62d2b3a6efbe3525dad4101be94cb15f9d5feea578af61bddf9d7ea150787a51ab97e4994f0778e97099b64f9b5e87fee7c2c97f07b9442bf8ae50c977ed094ce892be53d1fe5e9ac2405d7b7ba1d606385f68d070588b1276ddfbb2947de2a15f5cb8e3bc75b66eed634ccd980a79e5e8978ed51988b8da6354a7babe194d0ffa3a58a396375acab316e6c1b962268b7f7d9d3974975e7d687a6e7962d7f546a488152c97ac41e1da57de43963e2962afef0d7f8b9d9d3b7b819ecd596bbcd7f878d94ffcedb2105867efcbb356add24c9738ccf153ee58617c766bc2ed933f3fbffb1f60518b7ace8b8ed8f4b7505
Completely signed.
```

Alice now gives her previous secret
(7e5c4910874e226a549ff10cf8cafda2597241154b8862310cd27f056476b038) to Bob, ensuring she will not use
the previous commitment tx. Bob verifies the secret as follows:

```
hashsecret 7e5c4910874e226a549ff10cf8cafda2597241154b8862310cd27f056476b038

2cdfc5d839ee82115c187599fdee4651b21ca5c59d5676af3efcf32c09e82d66
```

Likewise Bob gives his previous secret (903fc1d134a0c5b25dd60db07eb9d8662103255de7473af417ebfa2f8daefcb9) to Alice, ensuring she will not use
the previous commitment tx. Alice verifies the secret as follows:

```
hashsecret 903fc1d134a0c5b25dd60db07eb9d8662103255de7473af417ebfa2f8daefcb9

3688455c8145cf45ac5ee293f6ad9eefad5125b06d8da8976ba5901d71178e93
```
At this point the only current commitment txs reflect
the intended balance of 4.4999 bars for Alice,
0.4499 for Bob and 5.0499 for the bet.

Let us now suppose Block 40500 passes without a proof
of Peirce's Law appearing. Since it would be too late
for Bob to retrieve the htlcptlc output of his commitment tx,
Alice has arguably won the bet. If the two parties cooperate,
they can simply publish new commitment txs (and revoke the old ones)
reflecting a balance of 9.5498 for Alice and 0.4499 for Bob.
It is obviously in Alice's interest to cooperate.
Bob could refuse to acknowledge his loss of the bet
and Alice could publish her most recent commitment tx.
After 50 confirmations, she could then retrieve the first and third
output of the commitment tx (9.5498 bars).
During those 50 blocks, Bob could still publish a proof of
Peirce's Law. If so, Alice and Bob would compete to spend the
third commitment tx after 50 confirmations.
(In this corner case, either can be argued to have won or lost the bet.)

On the other hand, suppose Bob did produce a proof of Peirce's Law
before Block 40500 and shows this proof to Alice. Again, if
both parties cooperate, they can publish new commitment txs
(and revoke the old ones) reflecting a balance of 4.4999 bars for Alice
and 5.4998 bars for Bob. If Alice refuses to acknowledge Bob has won the bet,
Bob can publish the commitment tx and publish the proof of Peirce's
Law on chain. After 50 confirmations (which should be before Block 40550),
Bob can spend the second and third outputs giving him 5.4998 bars.

# Layer 2

Creating, updating and closing payment channels by hand as above
can be done, but is tedious. The intention is that a second
process (implementing a "Layer 2" over Proofgold) would call
these commands and manage payment channels. In principle this
"Layer 2" could also combine payment channels into a lightning
network like the one currently active on the Bitcoin network (Poon Dryja 2016).

Many of the commands above can be given the keyword `json` as a last
argument and the output will be in json format.  A second process
could call the commands with this keyword when appropriate.

## References

[BIP0065] https://github.com/bitcoin/bips/blob/master/bip-0065.mediawiki

[BIP0068] https://github.com/bitcoin/bips/blob/master/bip-0068.mediawiki

[BIP0112] https://github.com/bitcoin/bips/blob/master/bip-0112.mediawiki

[BIP0113] https://github.com/bitcoin/bips/blob/master/bip-0113.mediawiki

[Poon Dryja 2016] Joseph Poon, Thaddeus Dryja. The Bitcoin Lightning
Network: Scalable Off-Chain Instant Payments
https://lightning.network/lightning-network-paper.pdf
