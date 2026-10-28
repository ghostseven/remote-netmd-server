## Remote NetMD
*Brings Wireless to NetMD Devices*

Remote NetMD lets you set up a NetMD server on, for example, a Raspberry Pi connected to a NetMD-capable deck. It's then possible to remotely control that deck with any device on the same network with the help of Web Minidisc Pro. The program will automatically detect it when a device disconnects and connects again, so it can be left running unattended.

### Setting it up

You need Node.js 20 or newer.

1. [Define the correct udev rules](https://github.com/glaubitz/linux-minidisc/tree/master/netmd/etc) on the Pi, so that the node application can access your device.
2. Clone this repository and enter its directory.
3. Run a script to generate the HTTPS self-signed certificates: `bash createhttpskeys.sh`
4. Install the dependencies with `npm install`
5. Run `npm start` (or `node index.js`)
6. Visit the page hosted at `https://<your pi's IP address>:11396/`, and acknowledge the security risk
7. Add it in Web Minidisc Pro, by clicking the 'Add Custom Device' in the connect screen's dropdown. Then, after filling in the address and the name you want to see the server displayed as in Web Minidisc Pro, you can select your device from the connect screen's dropdown and connect to it.

Run `node index.js --help` for the available options (port, HTTP instead of HTTPS, certificate paths).

### Running it as a service

To start the server automatically, create `/etc/systemd/system/remote-netmd.service`, adjusting the user and paths:

```ini
[Unit]
Description=Remote NetMD server
After=network-online.target

[Service]
User=pi
WorkingDirectory=/home/pi/remote-netmd-server
ExecStart=/usr/bin/node index.js
Restart=on-failure

[Install]
WantedBy=multi-user.target
```

Then run `sudo systemctl enable --now remote-netmd`.

### Supported features

- Listing the disc's contents, playback control
- Renaming the disc, tracks and groups, including full-width titles; creating and deleting groups
- Moving and deleting tracks, wiping the disc or just its titles
- Uploading tracks in SP, LP2 and LP4, and in mono SP on devices which support it natively
- Ejecting the disc, on devices which support it
- Downloading tracks (MZ-RH1 only), formatting discs to Hi-MD (on Hi-MD units), finalizing the disc

- The homebrew (factory) mode on Sony and Aiwa portables: ToC editing, ripping tracks with the exploits, SP and mono SP uploads of ATRAC files, firmware and RAM dumps, and the other homebrew features. The exploits run on the server.

Downloading tracks, mono SP uploads, finalizing, wiping the titles and formatting need a version of Web Minidisc Pro which supports Remote NetMD API revision 2. The homebrew mode needs revision 3. Older versions keep working, but don't offer these features.
