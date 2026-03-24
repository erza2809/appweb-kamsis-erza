// Variabel Global
let finalOutputData = null; 
let finalFileName = "hasil";
let isOutputText = true;

/*BASE64*/
const Base64Custom = {
    alphabet: 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/',
    encode: function(bytes) {
        let result = '';
        for (let i = 0; i < bytes.length; i += 3) {
            let b1 = bytes[i], b2 = i + 1 < bytes.length ? bytes[i + 1] : 0, b3 = i + 2 < bytes.length ? bytes[i + 2] : 0;
            let has2 = i + 1 < bytes.length, has3 = i + 2 < bytes.length;
            let c1 = (b1 >> 2) & 0x3F, c2 = ((b1 & 0x03) << 4) | ((b2 >> 4) & 0x0F);
            let c3 = ((b2 & 0x0F) << 2) | ((b3 >> 6) & 0x03), c4 = b3 & 0x3F;
            result += this.alphabet[c1] + this.alphabet[c2] + (has2 ? this.alphabet[c3] : '=') + (has3 ? this.alphabet[c4] : '=');
        }
        return result;
    },
    decode: function(str) {
        let bytes = [];
        if (str.length % 4 !== 0) throw new Error("Base64 decode gagal!");
        for (let i = 0; i < str.length; i += 4) {
            let c1 = this.alphabet.indexOf(str[i]), c2 = this.alphabet.indexOf(str[i + 1]);
            let c3 = str[i + 2] === '=' ? 0 : this.alphabet.indexOf(str[i + 2]);
            let c4 = str[i + 3] === '=' ? 0 : this.alphabet.indexOf(str[i + 3]);
            let b1 = (c1 << 2) | (c2 >> 4), b2 = ((c2 & 0x0F) << 4) | (c3 >> 2), b3 = ((c3 & 0x03) << 6) | c4;
            bytes.push(b1);
            if (str[i + 2] !== '=') bytes.push(b2);
            if (str[i + 3] !== '=') bytes.push(b3);
        }
        return new Uint8Array(bytes);
    },
    encodeStr: function(str) { return this.encode(new TextEncoder().encode(str)); },
    decodeStr: function(b64) { return new TextDecoder().decode(this.decode(b64)); }
};

/*RSA*/
const RSA = {
    modPow: function(base, exp, mod) {
        let res = 1n; base = base % mod;
        while (exp > 0n) {
            if (exp % 2n === 1n) res = (res * base) % mod;
            exp = exp / 2n; base = (base * base) % mod;
        }
        return res;
    },
    modInverse: function(e, phi) {
        let m0 = phi, t, q, x0 = 0n, x1 = 1n;
        if (phi === 1n) return 0n;
        while (e > 1n) { q = e / phi; t = phi; phi = e % phi; e = t; t = x0; x0 = x1 - q * x0; x1 = t; }
        return x1 < 0n ? x1 + m0 : x1;
    },
    generateKeys: function() {
        let p = 61n, q = 53n; 
        let n = p * q, phi = (p - 1n) * (q - 1n), e = 17n;
        return { pub: { e: e, n: n }, priv: { d: this.modInverse(e, phi), n: n } };
    },
    encrypt: function(msgBytes, pubKey) {
        return msgBytes.map(b => this.modPow(BigInt(b), pubKey.e, pubKey.n).toString());
    }
};

/*HASH 32 BIT*/
const Hash32 = {
    compute: function(dataBytes) {
        let hash = 0x811c9dc5; 
        for(let b of dataBytes){ hash ^= b; hash = (hash * 0x01000193) >>> 0; }
        return hash.toString(16).padStart(8, "0");
    }
};

/*FEISTEL CIPHER (CBC)*/
const BLOCK_SIZE = 8; const ROUNDS = 8;
const SBOX = [6,4,12,5,0,7,2,14,1,15,3,13,8,10,9,11];
const PBOX = [1,5,2,0,3,7,4,6];

function xorBytes(a, b) {
    let len = Math.min(a.length, b.length);
    let out = new Uint8Array(len);
    for(let i=0; i<len; i++) out[i] = a[i] ^ b[i];
    return out;
}

class FeistelCipher {
    constructor(keyBytes, ivBytes = null) {
        this.key = keyBytes;
        this.iv = ivBytes || crypto.getRandomValues(new Uint8Array(BLOCK_SIZE));
        this.keys = this.genKeys(this.key);
    }
    genKeys(key) {
        let keys = [];
        for(let i=0; i<ROUNDS; i++) {
            let shift = i % key.length;
            let k = new Uint8Array(key.length);
            k.set(key.slice(shift)); k.set(key.slice(0, shift), key.length - shift);
            keys.push(k);
        }
        return keys;
    }
    roundFunc(r, k) {
        let x = xorBytes(r, k);
        let outSub = new Uint8Array(x.length);
        for(let i=0; i<x.length; i++) outSub[i] = (SBOX[(x[i] >> 4) & 15] << 4) | SBOX[x[i] & 15];
        let outPer = new Uint8Array(outSub.length);
        for(let i=0; i<outSub.length; i++) {
            let val = 0;
            for(let bit=0; bit<8; bit++) val |= (((outSub[i] >> PBOX[bit]) & 1) << bit);
            outPer[i] = val;
        }
        return outPer;
    }
    feistelEncrypt(block) {
        let L = block.slice(0,4), R = block.slice(4,8);
        for(let k of this.keys) { let temp = R; R = xorBytes(L, this.roundFunc(R, k.slice(0,4))); L = temp; }
        return new Uint8Array([...R, ...L]);
    }
    feistelDecrypt(block) {
        let L = block.slice(0,4), R = block.slice(4,8);
        for(let i = this.keys.length - 1; i >= 0; i--) { let temp = R; R = xorBytes(L, this.roundFunc(R, this.keys[i].slice(0,4))); L = temp; }
        return new Uint8Array([...R, ...L]);
    }
    pad(data) {
        let padLen = BLOCK_SIZE - (data.length % BLOCK_SIZE);
        let out = new Uint8Array(data.length + padLen); out.set(data); out.fill(padLen, data.length);
        return out;
    }
    unpad(data) {
        let padLen = data[data.length - 1];
        if(padLen < 1 || padLen > BLOCK_SIZE) return data;
        return data.slice(0, data.length - padLen);
    }
    encryptCBC(data) {
        data = this.pad(data); let prev = this.iv; let out = [];
        for(let i=0; i<data.length; i+=BLOCK_SIZE) {
            let b = xorBytes(data.slice(i, i+BLOCK_SIZE), prev);
            let enc = this.feistelEncrypt(b); out.push(...enc); prev = enc;
        }
        return new Uint8Array(out);
    }
    decryptCBC(data) {
        let prev = this.iv; let out = [];
        for(let i=0; i<data.length; i+=BLOCK_SIZE) {
            let b = data.slice(i, i+BLOCK_SIZE);
            let dec = this.feistelDecrypt(b); dec = xorBytes(dec, prev); out.push(...dec); prev = b;
        }
        return this.unpad(new Uint8Array(out));
    }
}

function toggleKeyVisibility() {
    const keyInput = document.getElementById("key");
    const keyContainer = document.getElementById("keyContainer");
    keyContainer.classList.toggle('show-key');
    if (keyContainer.classList.contains('show-key')) {
        keyInput.type = "text";
        keyContainer.querySelector('.eye-toggle-btn').title = "Sembunyikan Kunci";
    } else {
        keyInput.type = "password";
        keyContainer.querySelector('.eye-toggle-btn').title = "Tampilkan Kunci";
    }
}

function toggleInputMode() {
    let mode = document.getElementById("inputType").value;
    document.getElementById("textInputArea").style.display = mode === "text" ? "block" : "none";
    document.getElementById("fileInputArea").style.display = mode === "file" ? "block" : "none";
}

function resetOutputUI() {
    document.getElementById("downloadBtn").style.display = "none";
    document.getElementById("previewContainer").style.display = "none";
    document.getElementById("outputText").value = "";
    finalOutputData = null;
}

async function getPlainBytesAndType() {
    let mode = document.getElementById("inputType").value;
    if (mode === "text") {
        let text = document.getElementById("inputText").value;
        if (!text) throw new Error("Teks kosong!");
        return { bytes: new TextEncoder().encode(text), type: "text" };
    } else {
        let file = document.getElementById("inputFile").files[0];
        if (!file) throw new Error("Pilih file terlebih dahulu!");
        let ext = file.name.split('.').pop().toLowerCase();
        let buffer = await file.arrayBuffer();
        return { bytes: new Uint8Array(buffer), type: ext };
    }
}

async function encryptData() {
    try {
        resetOutputUI();
        let keyStr = document.getElementById("key").value;
        if (!keyStr) throw new Error("Kunci kosong!");

        let inputData = await getPlainBytesAndType();
        let keyBytes = new TextEncoder().encode(keyStr);

        let cipher = new FeistelCipher(keyBytes);
        let hashVal = Hash32.compute(inputData.bytes);
        let cipherBytes = cipher.encryptCBC(inputData.bytes);

        let rsaKeys = RSA.generateKeys();
        let encKeyStr = RSA.encrypt(keyBytes, rsaKeys.pub).join('-');

        let token = [
            Base64Custom.encode(cipher.iv),
            Base64Custom.encodeStr(hashVal),
            Base64Custom.encodeStr(encKeyStr),
            Base64Custom.encodeStr(inputData.type),
            Base64Custom.encode(cipherBytes)
        ].join('.');

        document.getElementById("outputText").value = token;
        
        finalOutputData = token;
        finalFileName = "Token_Enkripsi.txt";
        isOutputText = true;
        document.getElementById("downloadBtn").style.display = "block";

    } catch (e) { alert("Enkripsi Gagal: " + e.message); }
}

async function decryptData() {
    try {
        resetOutputUI();
        let keyStr = document.getElementById("key").value;
        if (!keyStr) throw new Error("Kunci kosong!");

        let packet = "";
        let mode = document.getElementById("inputType").value;
        
        if (mode === "text") {
            packet = document.getElementById("inputText").value.trim();
        } else {
            let file = document.getElementById("inputFile").files[0];
            if (!file) throw new Error("Pilih file token .txt hasil enkripsi!");
            packet = await file.text();
            packet = packet.trim();
        }

        let parts = packet.split('.');
        if (parts.length !== 5) throw new Error("Format Token tidak valid!");

        let ivBytes = Base64Custom.decode(parts[0]);
        let originalHash = Base64Custom.decodeStr(parts[1]);
        let fileType = Base64Custom.decodeStr(parts[3]); 
        let cipherBytes = Base64Custom.decode(parts[4]);

        let userKeyBytes = new TextEncoder().encode(keyStr);
        let cipher = new FeistelCipher(userKeyBytes, ivBytes);
        let plainBytes = cipher.decryptCBC(cipherBytes);

        if (Hash32.compute(plainBytes) !== originalHash) {
            throw new Error("Peringatan Integritas! Password salah atau data rusak.");
        }

        if (fileType === "text") {
            let decodedText = new TextDecoder().decode(plainBytes);

            document.getElementById("outputText").value = decodedText;
        } else {
            document.getElementById("outputText").value = `File [.${fileType}] berhasil didekripsi. Silakan klik tombol Download Hasil atau lihat Preview di bawah.`;
            
            finalOutputData = plainBytes;
            finalFileName = "Hasil_Dekripsi." + fileType;
            isOutputText = false;
            document.getElementById("downloadBtn").style.display = "block";

            if (["png", "jpg", "jpeg", "gif", "bmp"].includes(fileType)) {
                let blob = new Blob([plainBytes], { type: "image/" + fileType });
                document.getElementById("previewImage").src = URL.createObjectURL(blob);
                document.getElementById("previewContainer").style.display = "block";
            }
        }
    } catch (e) { alert("Dekripsi Gagal: " + e.message); }
}

function downloadResult() {
    if (!finalOutputData) return;
    let blob;
    if (isOutputText) {
        blob = new Blob([finalOutputData], { type: "text/plain" });
    } else {
        blob = new Blob([finalOutputData], { type: "application/octet-stream" });
    }
    let url = URL.createObjectURL(blob);
    let a = document.createElement("a");
    a.href = url;
    a.download = finalFileName;
    a.click();
    URL.revokeObjectURL(url);
}