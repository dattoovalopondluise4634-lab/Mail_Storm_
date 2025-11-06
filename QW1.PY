import html
import logging
import os
import queue
import re
import tempfile
import smtplib
import base64
import threading
import webbrowser
import pandas as pd
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.image import MIMEImage
from email.mime.application import MIMEApplication
from datetime import datetime
import random
import string
import pytz
import time
import tkinter as tk
import customtkinter as ctk
from tkinter import messagebox, filedialog, Toplevel
import tkinter.simpledialog as simpledialog
from PIL import Image, ImageTk
from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from google.auth.transport.requests import Request
from googleapiclient.discovery import build
from tkinter.constants import END, DISABLED, NORMAL
import sys
import subprocess
import platform
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json

# WeasyPrint import with error handling
try:
    from weasyprint import HTML, CSS
    WEASYPRINT_AVAILABLE = True
except ImportError:
    WEASYPRINT_AVAILABLE = False
    print("WeasyPrint not available. PDF conversion will be disabled.")

# Define the Gmail API scope
GMAIL_SCOPES = ['https://www.googleapis.com/auth/gmail.send']

SMTP_PRESETS = {
    'gmail': {'host': 'smtp.gmail.com', 'port': 587, 'requires_tls': True, 'ssl': False},
    'gmail_ssl': {'host': 'smtp.gmail.com', 'port': 465, 'requires_tls': False, 'ssl': True},
    'outlook': {'host': 'smtp.office365.com', 'port': 587, 'requires_tls': True, 'ssl': False},
    'yahoo': {'host': 'smtp.mail.yahoo.com', 'port': 465, 'requires_tls': False, 'ssl': True},
    'aol': {'host': 'smtp.aol.com', 'port': 465, 'requires_tls': False, 'ssl': True},
    'att': {'host': 'smtp.mail.att.net', 'port': 465, 'requires_tls': False, 'ssl': True},
    'icloud': {'host': 'smtp.mail.me.com', 'port': 587, 'requires_tls': True, 'ssl': False},
    'zoho': {'host': 'smtp.zoho.com', 'port': 587, 'requires_tls': True, 'ssl': False},
    'custom': {'host': '', 'port': 587, 'requires_tls': True, 'ssl': False},
    'smtp': {'host': '', 'port': 587, 'requires_tls': True, 'ssl': False},
    'gmail_api': {'host': '', 'port': 0, 'requires_tls': False, 'ssl': False}
}

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("green")

# Constants for pauses/limits
PAUSE_MIN, PAUSE_MAX = 2, 5
GMAIL_LIMIT_EMAILS, GMAIL_LIMIT_TIME = 90, 90
MAX_MAIN_SENDERS, MAX_REPL_SENDERS = 10, 50
ATTACHMENT_MAX_SIZE_MB = 25

# Resource path helper for bundled .exe
def resource_path(relative_path):
    try:
        base = getattr(sys, '_MEIPASS', os.path.abspath(os.path.dirname(__file__)))
        full_path = os.path.join(base, relative_path)
        if not os.path.exists(full_path):
            print(f"Warning: Resource not found at {full_path}")
        return full_path
    except Exception as e:
        print(f"Error accessing resource path for {relative_path}: {str(e)}")
        return os.path.join(os.path.abspath(os.path.dirname(__file__)), relative_path)

def add_bin_to_path():
    bin_dir = resource_path("bin")
    if os.path.exists(bin_dir):
        os.environ["PATH"] = bin_dir + os.pathsep + os.environ.get("PATH", "")
    else:
        print(f"Warning: bin directory not found at {bin_dir}")

add_bin_to_path()

WKHTMLTOIMAGE_PATH = resource_path("bin/wkhtmltoimage.exe")

class Devon:
    def __init__(self, app):
        self.app = app
        app.title("MAIL_STORM v2.5")
        app.geometry("900x630")
        app.resizable(False, False)
        
        # Load configuration
        self.config = self.load_config()
        
        # Thread management
        self.sending_thread = None
        self.stop_event = threading.Event()
        self.pause_event = threading.Event()
        
        # Email tracking
        self.sent_emails = set()
        self.sent_emails_lock = threading.Lock()
        self.emails_sent_lock = threading.Lock()
        self.emails_sent = 0
        self.total_emails = 0
        
        # Sender management
        self.sender_accounts = []
        self.replacement_senders = []
        self.failed_senders = []
        self.sender_accounts_lock = threading.Lock()
        self.sender_logs = {}
        self.sender_logs_lock = threading.Lock()
        self.sender_progress_lock = threading.Lock()
        self.sender_progress = {}
        self.sender_last_sent = {}
        self.sender_recipient_lists = {}
        self.sender_rate_limits = {}
        self.sender_rate_locks = {}
        
        # GUI elements
        self.image_preview_windows = []
        self.subjects = []
        self.max_concurrent_threads = self.config['max_concurrent_threads']
        self.gui_queue = queue.Queue(maxsize=self.config['gui_queue_size'])
        self.app.after(100, self.check_gui_queue)
        self.attachments = []
        self.sending_lock = threading.Lock()
        self.subject_lines = []
        self.subject_file_path = None
        self.text_subject_path = None
        self.gmail_credentials_path = None
        self.selected_emails = set()
        self.selected_emails_lock = threading.Lock()
        self.sender_names = self.load_sender_names()
        self.log_window = None
        self.summary_label = None
        self.unsubscribe_link = "https://example.com/unsubscribe"
        
        # File paths
        self.csv_file_path = None
        self.text_file_path = None
        self.sender_csv_file_path = None
        
        # Sender Manager attributes
        self.sender_manager_window = None
        self.sender_rows = []
        self.replacement_rows = []
        self.failed_rows = []
        self.main_rows = []
        self.repl_rows = []
        self.status_filter_var = None
        self.manager_search_entry = None
        self.main_inner = None
        self.repl_inner = None
        self.failed_inner = None
        self.main_canvas = None
        self.repl_canvas = None
        self.failed_canvas = None
        self.test_progress = None
        self.status_message = None
        self.stop_test = False
        self.refresh_debounce_id = None
        self.filtered_cache = {}
        self.count_labels = {}
        
        # Variables
        self.format_var = tk.StringVar(value="HTML")
        self.html_var = tk.BooleanVar(value=False)
        self.random_pause_var = tk.BooleanVar(value=False)
        self.auto_pause_var = tk.BooleanVar(value=False)
        self.auto_pause_count = tk.StringVar(value=str(self.config['auto_pause_count']))
        self.include_unsubscribe_var = tk.BooleanVar(value=False)
        self.random_name_var = tk.BooleanVar()
        self.send_mode_var = tk.StringVar(value="Multiple SMTP")
        self.select_all_var = tk.BooleanVar(value=False)
        
        if not WEASYPRINT_AVAILABLE:
            self.format_var.set("HTML")
            print("PDF format disabled: WeasyPrint not installed.")

        self.configure = {
            "send_mode": "send_manually",
            "email_list": [],
            "subject_mode": "custom",
            "custom_subject": "",
            "message": "",
            "attachment": None,
            "timer_interval": "1 sec"
        }

        self.setup_ui()
        
        # Load previous progress if exists
        self.check_resume_progress()

    def load_config(self):
        """Load configuration from file."""
        config_path = 'config.json'
        default_config = {
            'max_main_senders': 10,
            'max_repl_senders': 50,
            'pause_min': 2,
            'pause_max': 5,
            'gmail_limit_emails': 90,
            'gmail_limit_time': 90,
            'attachment_max_size_mb': 25,
            'max_concurrent_threads': 10,
            'gui_queue_size': 4000,
            'default_timer': 5,
            'auto_pause_count': 100
        }
        
        if os.path.exists(config_path):
            try:
                with open(config_path, 'r') as f:
                    loaded_config = json.load(f)
                    default_config.update(loaded_config)
                print("Configuration loaded from file")
            except Exception as e:
                print(f"Error loading config: {str(e)}, using defaults")
        else:
            # Save default config
            try:
                with open(config_path, 'w') as f:
                    json.dump(default_config, f, indent=4)
            except:
                pass
        
        return default_config

    def save_config(self):
        """Save current configuration to file."""
        try:
            with open('config.json', 'w') as f:
                json.dump(self.config, f, indent=4)
            self.update_log("Configuration saved")
        except Exception as e:
            self.update_log(f"Error saving config: {str(e)}")

    def setup_ui(self):
        """Setup all UI elements."""
        # Login label
        login_label = ctk.CTkLabel(self.app, text="Login ID: Devon", text_color="lime", font=("Arial", 14, "bold"))
        login_label.place(x=10, y=10)
        ctk.CTkLabel(self.app, text="MailStorm v2.5", text_color="lime", font=("Romantic", 20, "bold", "italic")).place(x=720, y=10)

        # Subject section
        ctk.CTkLabel(self.app, text="Subject", font=("Arial", 12, "bold"), text_color="#FFFFFF").place(x=10, y=50)
        self.subject_entry = ctk.CTkEntry(self.app, placeholder_text="Enter Subject line", width=200)
        self.subject_entry.place(x=100, y=50)
        
        self.subject_var = tk.StringVar(value="Subjects")
        self.subject_comb = ctk.CTkComboBox(self.app, width=80, variable=self.subject_var,
                                           values=["Auto Attach Name and Custom", "Attach subject From TXT File",
                                                   "Auto Attach Name and CSV", "Attach Subject from CSV", "Write My Own"],
                                           command=self.subject_option_changed)
        self.subject_comb.place(x=305, y=50)
        
        self.text_subject_label = ctk.CTkLabel(self.app, text="", font=("Arial", 12, "bold"), text_color="blue")
        self.text_subject_label.place(x=10, y=80)

        # Sender Name section
        ctk.CTkLabel(self.app, text="Sender Name", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=10, y=85)
        self.sender_name_entry = ctk.CTkEntry(self.app, placeholder_text="Enter Sender Name", width=180)
        self.sender_name_entry.place(x=100, y=85)
        ctk.CTkButton(self.app, text="🎲Pick", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=50, command=self.pick_random_name).place(x=285, y=85)
        ctk.CTkCheckBox(self.app, text="_R", font=("Arial", 13, "bold"), text_color="#FFFFFF", border_width=3,
                        checkbox_width=20, checkbox_height=20, border_color="#C74AD8",
                        variable=self.random_name_var).place(x=345, y=85)

        # Sender Email section
        ctk.CTkLabel(self.app, text="Sender Email", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=10, y=120)
        self.sender_email_entry = ctk.CTkEntry(self.app, placeholder_text="Enter Sender Email", width=270)
        self.sender_email_entry.place(x=100, y=120)
        
        # Password section
        ctk.CTkLabel(self.app, text="Password", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=10, y=155)
        self.sender_password_entry = ctk.CTkEntry(self.app, placeholder_text="Enter Password/App-Specific Password", width=240, show="*")
        self.sender_password_entry.place(x=100, y=155)
        
        # Password toggle button
        eye_open_path = resource_path("eye_open.png")
        eye_closed_path = resource_path("eye_closed.png")
        
        try:
            self.eye_open_img = ImageTk.PhotoImage(Image.open(eye_open_path).resize((20, 20)))
            self.eye_closed_img = ImageTk.PhotoImage(Image.open(eye_closed_path).resize((20, 20)))
            self.password_toggle_button = ctk.CTkButton(
                self.app, image=self.eye_closed_img, text="", width=30, height=25,
                command=self.toggle_password_visibility, fg_color="green", hover_color="#1A8B53"
            )
        except:
            self.password_toggle_button = ctk.CTkButton(
                self.app, text="👁️", width=30, height=25,
                command=self.toggle_password_visibility, fg_color="green", hover_color="#1A8B53"
            )
        self.password_toggle_button.place(x=345, y=155)

        # Body section
        ctk.CTkLabel(self.app, text="Body:", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=10, y=185)
        self.message_text = ctk.CTkCheckBox(self.app, text="HTML Body", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                                           border_width=3, checkbox_width=20, checkbox_height=20, border_color="#C74AD8",
                                           variable=self.html_var)
        self.message_text.place(x=280, y=190)
        
        self.body_textbox = ctk.CTkTextbox(self.app, width=370, height=100, fg_color="#020102", font=("Arial", 13, "bold"),
                                          scrollbar_button_color='red', scrollbar_button_hover_color='yellow', wrap='word')
        self.body_textbox.place(x=10, y=220)
        
        # Bind keyboard shortcuts
        self.body_textbox.bind('<Control-z>', lambda event: self.undo(self.body_textbox))
        self.body_textbox.bind('<Control-y>', lambda event: self.redo(self.body_textbox))
        self.body_textbox.bind('<Control-a>', lambda event: self.select_all(self.body_textbox))
        
        # Context menu for body
        self.body_menu = tk.Menu(self.app, tearoff=0)
        self.body_menu.add_command(label="Copy", command=lambda: self.copy_text(self.body_textbox))
        self.body_menu.add_command(label="Paste", command=lambda: self.paste_text(self.body_textbox))
        self.body_menu.add_command(label="Delete", command=lambda: self.delete_text(self.body_textbox))
        self.body_menu.add_command(label="Select All", command=lambda: self.select_all(self.body_textbox))
        self.body_textbox.bind("<Button-3>", lambda event: self.show_context_menu(event, self.body_menu))

        # Tools section
        ctk.CTkLabel(self.app, text="TOOLZ:", font=("Arial", 16, "bold"), text_color="#FFFFFF").place(x=10, y=325)
        ctk.CTkButton(self.app, text="#TAG#", font=("Arial", 12, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=60, command=self.show_tags_popup).place(x=100, y=325)
        
        # HTML preview and add buttons
        ctk.CTkButton(self.app, text="🔎Preview", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=80, height=18, command=self.preview_html).place(x=555, y=210)
        ctk.CTkButton(self.app, text="Add HTML", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=80, height=18, command=self.add_html_file).place(x=640, y=210)

        # HTML textbox
        self.html_textbox = ctk.CTkTextbox(self.app, width=300, height=150, fg_color="#020102", font=("Arial", 13, "bold"),
                                      scrollbar_button_color='red', scrollbar_button_hover_color='yellow', wrap='word')
        self.html_textbox.place(x=419, y=240)
        
        # Bind keyboard shortcuts for HTML
        self.html_textbox.bind('<Control-z>', lambda event: self.undo(self.html_textbox))
        self.html_textbox.bind('<Control-y>', lambda event: self.redo(self.html_textbox))
        self.html_textbox.bind('<Control-a>', lambda event: self.select_all(self.html_textbox))
        
        # Context menu for HTML
        self.html_menu = tk.Menu(self.app, tearoff=0)
        self.html_menu.add_command(label="Copy", command=lambda: self.copy_text(self.html_textbox))
        self.html_menu.add_command(label="Paste", command=lambda: self.paste_text(self.html_textbox))
        self.html_menu.add_command(label="Delete", command=lambda: self.delete_text(self.html_textbox))
        self.html_menu.add_command(label="Select All", command=lambda: self.select_all(self.html_textbox))
        self.html_textbox.bind("<Button-3>", lambda event: self.show_context_menu(event, self.html_menu))

        # Image label
        self.image_label = ctk.CTkLabel(self.app, text="", image=None)
        self.image_label.place(x=419, y=390)

        # Attachment section
        self.attach_button = ctk.CTkButton(self.app, text="Attach Files", font=("Arial", 12, "bold"),
                                          text_color="#FFFFFF", fg_color="#1A8B53", width=60, command=self.attach_file)
        self.attach_button.place(x=300, y=325)
        
        self.file_label = ctk.CTkLabel(self.app, text="", font=("Arial", 12, "bold"), text_color="blue")
        self.file_label.place(x=10, y=410)
        
        self.remove_file_button = ctk.CTkButton(self.app, text="Remove Files", font=("Arial", 12, "bold"),
                                               text_color="#FFFFFF", fg_color="red", width=60, command=self.remove_file)
        self.remove_file_button.place_forget()

        # Recipient Options
        ctk.CTkLabel(self.app, text="Recipient Options:", font=("Arial", 14, "bold"), text_color="#FFFFFF").place(x=15, y=355)
        self.actions_var = tk.StringVar(value="MANUAL")
        self.actions_combo = ctk.CTkComboBox(
            self.app, values=["MANUAL", "TEXT/CSV"], variable=self.actions_var,
            state='readonly', width=140, height=20, command=self.on_combobox_change
        )
        self.actions_combo.place(x=10, y=380)
        
        self.recipient_label = ctk.CTkLabel(self.app, text="", font=("Arial", 12, "bold"), text_color="blue")
        self.recipient_label.place(x=10, y=440)

        # Recipient input
        self.to_entry = ctk.CTkEntry(self.app, placeholder_text="MANUAL Recipient", width=230)
        self.to_entry.place(x=419, y=50)
        self.to_entry.bind('<Return>', self.add_email)
        
        self.add_email_button = ctk.CTkButton(self.app, text="Import Recipient", font=("Arial", 13, "bold"),
                                             text_color="#FFFFFF", fg_color="#1A8B53", width=60, command=self.add_email)
        self.add_email_button.place(x=660, y=50)
        
        ctk.CTkButton(self.app, text="Delete", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=60, command=self.delete_selected_emails).place(x=825, y=50)

        # Tester recipient textbox
        self.tester_recipient_textbox = ctk.CTkTextbox(
            self.app, width=230, height=110, state='disabled', fg_color="#020102", font=("Arial", 13, "bold"),
            scrollbar_button_color='red', scrollbar_button_hover_color='yellow', wrap='word'
        )
        self.tester_recipient_textbox.place(x=419, y=90)
        self.tester_recipient_textbox.bind("<Button-1>", self.start_selection)
        self.tester_recipient_textbox.bind("<B1-Motion>", self.extend_selection)

        # Recipient textbox (CSV/TEXT)
        self.recipient_textbox = ctk.CTkTextbox(
            self.app, width=230, height=110, state='disabled', fg_color="#020102", font=("Arial", 13, "bold"),
            scrollbar_button_color='red', scrollbar_button_hover_color='yellow', wrap='word'
        )
        self.recipient_textbox.place(x=660, y=90)
        self.recipient_textbox.bind("<Button-1>", self.start_selection)
        self.recipient_textbox.bind("<B1-Motion>", self.extend_selection)

        # Select all checkbox
        self.select_all_checkbox = ctk.CTkCheckBox(
            self.app, text="Select All Emails", variable=self.select_all_var,
            command=self.select_all_emails, font=("Arial", 13, "bold"), text_color="white",
            border_width=3, checkbox_width=20, checkbox_height=20, border_color="#C74AD8"
        )
        self.select_all_checkbox.place(x=419, y=205)

        # Sending Options
        ctk.CTkLabel(self.app, text="Sending Options:", font=("Arial", 14, "bold"), text_color="#FFFFFF").place(x=245, y=355)
        self.send_mode_combo = ctk.CTkComboBox(self.app, values=["Multiple SMTP", "Gmail API", "iCloud SMTP", "Gmail SMTP"],
                                      variable=self.send_mode_var, state='readonly', width=140, height=20,
                                      command=self.update_api_smtp)
        self.send_mode_combo.place(x=240, y=380)
        
        self.smtp_label = ctk.CTkLabel(self.app, text="", font=("Arial", 12, "bold"), text_color="blue")
        self.smtp_label.place(x=10, y=470)
        
        self.attach_senders_button = ctk.CTkButton(self.app, text="Attach Senders", font=("Arial", 13, "bold"),
                                          text_color="#FFFFFF", fg_color="blue", width=60,
                                          command=self.open_sender_manager)
        self.attach_senders_button.place(x=10, y=470)
        self.attach_senders_button.place_forget()
        
        
        self.remove_smtp_button = ctk.CTkButton(self.app, text="Remove Senders", font=("Arial", 12, "bold"),
                                               text_color="#FFFFFF", fg_color="red", width=60, command=self.remove_sender_csv_file)
        self.remove_smtp_button.place_forget()

        # Unsubscribe section
        unsubscribe_label = ctk.CTkLabel(self.app, text="Link:", font=("Arial", 13, "bold"), text_color="#FFFFFF")
        unsubscribe_label.place(x=390, y=515)
        self.unsubscribe_entry = ctk.CTkEntry(self.app, placeholder_text="Enter Unsubscribe Link", width=200)
        self.unsubscribe_entry.insert(0, self.unsubscribe_link)
        self.unsubscribe_entry.place(x=430, y=515)
        self.unsubscribe_entry.bind("<KeyRelease>", lambda e: self.update_unsubscribe_link())
        
        self.include_unsubscribe_check = ctk.CTkCheckBox(self.app, text="Include Unsubscribe Link", font=("Arial", 13, "bold"),
                                                         text_color="#FFFFFF", border_width=3, checkbox_width=20,
                                                         checkbox_height=20, border_color="#C74AD8", 
                                                         variable=self.include_unsubscribe_var)
        self.include_unsubscribe_check.place(x=419, y=480)

        # Output Format
        ctk.CTkLabel(self.app, text="Output Format:", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=419, y=395)
        ctk.CTkRadioButton(self.app, text="HTML", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                           border_color="#C74AD8", variable=self.format_var, value="HTML").place(x=520, y=400)
        ctk.CTkRadioButton(self.app, text="JPG", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                           border_color="#C74AD8", variable=self.format_var, value="JPG").place(x=600, y=400)
        pdf_radio = ctk.CTkRadioButton(self.app, text="PDF", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                                      border_color="#C74AD8", variable=self.format_var, value="PDF")
        pdf_radio.place(x=670, y=400)
        if not WEASYPRINT_AVAILABLE:
            pdf_radio.configure(state="disabled")

        # Log window button
        ctk.CTkButton(self.app, text="View Logs", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=80, command=self.show_log_window).place(x=750, y=400)

        # Activity log
        ctk.CTkLabel(self.app, text="Activity:", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=735, y=210)
        ctk.CTkButton(self.app, text="Clear Log", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=80, height=20, command=self.clear_log).place(x=810, y=210)
        self.log_text = ctk.CTkTextbox(self.app, width=166, height=150, state='disabled', fg_color="#020102",
                                       font=("Arial", 13, "bold"), scrollbar_button_color='red',
                                       scrollbar_button_hover_color='yellow', wrap='word')
        self.log_text.place(x=725, y=240)

        # Status section
        ctk.CTkLabel(self.app, text="Status :", text_color="white", font=("Arial", 13, "bold")).place(x=10, y=500)
        self.status_label = ctk.CTkLabel(self.app, text="Inbox impact starts with you", width=300, anchor="w", 
                                        text_color="lime", font=("Arial", 13, "bold"))
        self.status_label.place(x=80, y=500)
        
        # Progress bar
        self.progress_bar = ctk.CTkProgressBar(self.app, width=880)
        self.progress_bar.place(x=10, y=550)
        self.progress_bar.set(0)
        self.progress_label = ctk.CTkLabel(self.app, text="Progress: 0 / 0", font=("Arial", 13, "bold"), text_color="Yellow")
        self.progress_label.place(x=10, y=520)

        # Email batch and timer settings
        ctk.CTkLabel(self.app, text="Emails:", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=419, y=440)
        self.emails_per_batch = ctk.CTkEntry(self.app, width=50)
        self.emails_per_batch.place(x=480, y=440)
        
        ctk.CTkLabel(self.app, text="sec:", font=("Arial", 13, "bold"), text_color="#FFFFFF").place(x=570, y=440)
        self.timer_entry = ctk.CTkEntry(self.app, width=50)
        self.timer_entry.insert(0, str(self.config['default_timer']))
        self.timer_entry.place(x=620, y=440)
        self.timer_entry.bind("<KeyRelease>", self.validate_numeric_entry)
        
        ctk.CTkCheckBox(self.app, text="Random Pause", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                        border_width=3, checkbox_width=20, checkbox_height=20, border_color="#C74AD8",
                        variable=self.random_pause_var).place(x=690, y=440)
        
        ctk.CTkCheckBox(self.app, text="Auto Pause", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                        border_width=3, checkbox_width=20, checkbox_height=20, border_color="#C74AD8",
                        variable=self.auto_pause_var).place(x=690, y=500)
        
        self.auto_pause_entry = ctk.CTkEntry(self.app, width=50, textvariable=self.auto_pause_count)
        self.auto_pause_entry.place(x=790, y=500)
        self.auto_pause_entry.bind("<KeyRelease>", self.validate_numeric_entry)

        # Test sender combo
        self.test_sender_var = tk.StringVar(value="")
        self.test_sender_combo = ctk.CTkComboBox(self.app, values=[], variable=self.test_sender_var,
                                                 width=240, height=24)
        self.test_sender_combo.place(x=320, y=10)
        
        self.test_send_button = ctk.CTkButton(self.app, text="Test Send", width=90, height=24,
                                              font=("Arial", 13, "bold"), text_color="#FFFFFF",
                                              fg_color="#1A8B53", command=self.test_send_from_selected)
        self.test_send_button.place(x=600, y=10)

        # Action buttons
        self.reset_button = ctk.CTkButton(self.app, text="Reset", font=("Arial", 13, "bold"),
                                         text_color="#FFFFFF", fg_color="Red", height=20, width=160,
                                         command=self.reset_form)
        self.reset_button.place(x=10, y=590)
        
        self.send_button = ctk.CTkButton(self.app, text="Send Email", font=("Arial", 13, "bold"),
                                        text_color="#FFFFFF", height=20, fg_color="blue", width=500,
                                        command=self.start_send_thread)
        self.send_button.place(x=200, y=590)
        
        self.pause_button = ctk.CTkButton(self.app, text="Pause", font=("Arial", 13, "bold"),
                                  text_color="#FFFFFF", height=20, width=120, fg_color="#1A8B53",
                                  command=self.toggle_pause)
        self.pause_button.place(x=710, y=590)

        self.stop_button = ctk.CTkButton(self.app, text="Stop", font=("Arial", 13, "bold"),
                                 text_color="#FFFFFF", height=20, width=120, fg_color="red",
                                 command=self.stop_sending)
        self.stop_button.place_forget()
        
        # Bind delete key
        self.app.bind("<Delete>", self.handle_delete_key)
        
        # Setup context menus for all inputs
        self.setup_context_menus()

    def setup_context_menus(self):
        """Setup context menus for all input fields."""
        # Subject entry
        self.subject_menu = tk.Menu(self.app, tearoff=0)
        self.subject_menu.add_command(label="Copy", command=lambda: self.copy_text(self.subject_entry))
        self.subject_menu.add_command(label="Paste", command=lambda: self.paste_text(self.subject_entry))
        self.subject_menu.add_command(label="Delete", command=lambda: self.delete_text(self.subject_entry))
        self.subject_menu.add_command(label="Select All", command=lambda: self.select_all(self.subject_entry))
        self.subject_entry.bind("<Button-3>", lambda event: self.show_context_menu(event, self.subject_menu))
        
        # Sender email entry
        self.sender_email_menu = tk.Menu(self.app, tearoff=0)
        self.sender_email_menu.add_command(label="Copy", command=lambda: self.copy_text(self.sender_email_entry))
        self.sender_email_menu.add_command(label="Paste", command=lambda: self.paste_text(self.sender_email_entry))
        self.sender_email_menu.add_command(label="Delete", command=lambda: self.delete_text(self.sender_email_entry))
        self.sender_email_menu.add_command(label="Select All", command=lambda: self.select_all(self.sender_email_entry))
        self.sender_email_entry.bind("<Button-3>", lambda event: self.show_context_menu(event, self.sender_email_menu))
        
        # Sender password entry
        self.sender_password_menu = tk.Menu(self.app, tearoff=0)
        self.sender_password_menu.add_command(label="Copy", command=lambda: self.copy_text(self.sender_password_entry))
        self.sender_password_menu.add_command(label="Paste", command=lambda: self.paste_text(self.sender_password_entry))
        self.sender_password_menu.add_command(label="Delete", command=lambda: self.delete_text(self.sender_password_entry))
        self.sender_password_menu.add_command(label="Select All", command=lambda: self.select_all(self.sender_password_entry))
        self.sender_password_entry.bind("<Button-3>", lambda event: self.show_context_menu(event, self.sender_password_menu))
        
        # Sender name entry
        self.sender_name_menu = tk.Menu(self.app, tearoff=0)
        self.sender_name_menu.add_command(label="Copy", command=lambda: self.copy_text(self.sender_name_entry))
        self.sender_name_menu.add_command(label="Paste", command=lambda: self.paste_text(self.sender_name_entry))
        self.sender_name_menu.add_command(label="Delete", command=lambda: self.delete_text(self.sender_name_entry))
        self.sender_name_menu.add_command(label="Select All", command=lambda: self.select_all(self.sender_name_entry))
        self.sender_name_entry.bind("<Button-3>", lambda event: self.show_context_menu(event, self.sender_name_menu))
        
        # Tester recipient textbox
        self.tester_recipient_menu = tk.Menu(self.app, tearoff=0)
        self.tester_recipient_menu.add_command(label="Copy", command=lambda: self.copy_text(self.tester_recipient_textbox))
        self.tester_recipient_menu.add_command(label="Paste", command=lambda: self.paste_text(self.tester_recipient_textbox))
        self.tester_recipient_menu.add_command(label="Delete", command=lambda: self.delete_text(self.tester_recipient_textbox))
        self.tester_recipient_menu.add_command(label="Select All", command=lambda: self.select_all(self.tester_recipient_textbox))
        self.tester_recipient_textbox.bind("<Button-3>", lambda event: self.show_context_menu(event, self.tester_recipient_menu))

        # Recipient textbox
        self.recipient_menu = tk.Menu(self.app, tearoff=0)
        self.recipient_menu.add_command(label="Copy", command=lambda: self.copy_text(self.recipient_textbox))
        self.recipient_menu.add_command(label="Paste", command=lambda: self.paste_text(self.recipient_textbox))
        self.recipient_menu.add_command(label="Delete", command=lambda: self.delete_text(self.recipient_textbox))
        self.recipient_menu.add_command(label="Select All", command=lambda: self.select_all(self.recipient_textbox))
        self.recipient_textbox.bind("<Button-3>", lambda event: self.show_context_menu(event, self.recipient_menu))

        # To entry
        self.to_entry_menu = tk.Menu(self.app, tearoff=0)
        self.to_entry_menu.add_command(label="Copy", command=lambda: self.copy_text(self.to_entry))
        self.to_entry_menu.add_command(label="Paste", command=lambda: self.paste_text(self.to_entry))
        self.to_entry_menu.add_command(label="Delete", command=lambda: self.delete_text(self.to_entry))
        self.to_entry_menu.add_command(label="Select All", command=lambda: self.select_all(self.to_entry))
        self.to_entry.bind("<Button-3>", lambda event: self.show_context_menu(event, self.to_entry_menu))

    def load_sender_names(self):
        """Load sender names from file."""
        try:
            path = resource_path('sender_names.txt')
            with open(path, 'r', encoding='utf-8') as file:
                names = [line.strip() for line in file if line.strip()]
                return names if names else ["Default Sender"]
        except FileNotFoundError:
            self.update_log("Warning: sender_names.txt not found. Using default name.")
            return ["Default Sender"]
        except Exception as e:
            self.update_log(f"Error loading sender names: {str(e)}")
            return ["Default Sender"]

    def check_resume_progress(self):
        """Check if there's a previous incomplete send to resume."""
        saved_state = self.load_progress_state()
        if saved_state and saved_state.get('emails_sent', 0) < saved_state.get('total_emails', 0):
            if messagebox.askyesno("Resume Sending", 
                f"Found incomplete send: {saved_state['emails_sent']}/{saved_state['total_emails']} emails sent.\n\nDo you want to resume?"):
                with self.sent_emails_lock:
                    self.sent_emails = set(saved_state.get('sent_emails', []))
                with self.sender_progress_lock:
                    self.sender_progress = saved_state.get('sender_progress', {})
                self.update_log(f"Resumed from previous state: {len(self.sent_emails)} emails already sent")

    def save_progress_state(self):
        """Save current sending state for crash recovery."""
        state = {
            'emails_sent': self.emails_sent,
            'total_emails': self.total_emails,
            'sender_progress': self.sender_progress,
            'sent_emails': list(self.sent_emails),
            'timestamp': datetime.now().isoformat()
        }
        
        try:
            with open('progress_state.json', 'w') as f:
                json.dump(state, f, indent=2)
        except Exception as e:
            self.update_log(f"Error saving progress: {str(e)}")

    def load_progress_state(self):
        """Load previous sending state if exists."""
        if not os.path.exists('progress_state.json'):
            return None
        
        try:
            with open('progress_state.json', 'r') as f:
                state = json.load(f)
            
            # Check if state is recent (within 24 hours)
            timestamp = datetime.fromisoformat(state['timestamp'])
            if (datetime.now() - timestamp).days > 1:
                return None
            
            return state
        except Exception as e:
            self.update_log(f"Error loading progress: {str(e)}")
            return None

    def normalize_csv_columns(self, df):
        """Normalize DataFrame columns to lowercase and map common variations."""
        df.columns = [c.strip().lower().replace(' ', '_') for c in df.columns]
        
        # Map common variations
        column_mappings = {
            'e-mail': 'email',
            'e_mail': 'email',
            'mail': 'email',
            'pwd': 'password',
            'pass': 'password',
            'smtp_host': 'host',
            'smtp_port': 'port',
            'firstname': 'name',
            'first_name': 'name',
            'surname': 'last_name',
            'lastname': 'last_name'
        }
        
        df.rename(columns=column_mappings, inplace=True)
        return df

    def check_rate_limit(self, sender_email, limit_per_minute=30):
        """Check if sender exceeded rate limit."""
        if sender_email not in self.sender_rate_limits:
            self.sender_rate_limits[sender_email] = []
            self.sender_rate_locks[sender_email] = threading.Lock()
        
        with self.sender_rate_locks[sender_email]:
            now = time.time()
            # Remove timestamps older than 1 minute
            self.sender_rate_limits[sender_email] = [
                t for t in self.sender_rate_limits[sender_email] 
                if now - t < 60
            ]
            
            if len(self.sender_rate_limits[sender_email]) >= limit_per_minute:
                sleep_time = 60 - (now - self.sender_rate_limits[sender_email][0])
                self.update_log(f"Rate limit hit for {sender_email}, sleeping {sleep_time:.1f}s")
                time.sleep(sleep_time)
                self.sender_rate_limits[sender_email] = []
            
            self.sender_rate_limits[sender_email].append(now)

    def check_duplicate_sender(self, new_email):
        """Check if sender email already exists."""
        with self.sender_accounts_lock:
            all_senders = self.sender_accounts + self.replacement_senders + self.failed_senders
            return any(s['email'].lower() == new_email.lower() for s in all_senders)

    # ==================== GENERATOR METHODS ====================
    
    def generate_transaction_id(self):
        """Generate random transaction ID."""
        integer_part = ''.join(random.choices(string.digits, k=8))
        fractional_part = ''.join(random.choices(string.digits, k=8))
        return f"C-{integer_part}-{fractional_part}"

    def generate_membership_id(self):
        """Generate random membership ID."""
        return ''.join(random.choices(string.ascii_letters + string.digits, k=10))

    def generate_customer_id(self):
        """Generate random customer ID."""
        return ''.join(random.choices(string.digits, k=9))

    def generate_amount(self):
        """Generate random amount."""
        integer_part = ''.join(random.choices(string.digits, k=3))
        fractional_part = ''.join(random.choices(string.digits, k=2))
        return f"USD{integer_part}.{fractional_part}"

    def generate_random_filename(self):
        """Generate random filename."""
        integer_part1 = ''.join(random.choices(string.digits, k=2))
        integer_part2 = ''.join(random.choices(string.digits, k=2))
        integer_part3 = ''.join(random.choices(string.digits, k=6))
        return f"O-{integer_part1}-{integer_part2}-{integer_part3}"

    # ==================== SUBJECT METHODS ====================
    
    def get_subject(self, name, last_name, row=None, customer_id=None, membership_id=None):
        """Generate email subject based on selected mode."""
        est = pytz.timezone('US/Eastern')
        current_time = datetime.now(est).strftime('%B %d, %Y, %I:%M %p').replace(' 0', '')
        customer_id = customer_id or self.generate_customer_id()
        membership_id = membership_id or self.generate_membership_id()
        selected_option = self.subject_var.get()
        subject = self.subject_entry.get() if selected_option in ["Write My Own", "Auto Attach Name and Custom"] else ""

        if selected_option == "Attach Subject from CSV":
            if row is not None and isinstance(row, dict) and 'subject' in row and row['subject']:
                return f"{row['subject']}"
            self.update_log("Warning: No valid subject found in CSV row, using default.")
            return f"No Subject {current_time}"
        elif selected_option == "Write My Own":
            return subject.replace('[[customer_id]]', customer_id).replace('[[membership_id]]', membership_id)
        elif selected_option == "Auto Attach Name and Custom":
            return f"{name} {last_name}, {subject} {current_time}"
        elif selected_option == "Auto Attach Name and CSV":
            if row is not None and isinstance(row, dict) and 'subject' in row and row['subject']:
                return f"{name} {last_name}, {row['subject']} {current_time}"
            self.update_log("Warning: No valid subject found in CSV row, using default.")
            return f"{name} {last_name}, No Subject {current_time}"
        elif selected_option == "Attach subject From TXT File":
            subject_from_txt = self.get_random_subject()
            return f"{subject_from_txt}"
        
        self.update_log("Warning: Invalid subject option selected, using default.")
        return f"No Subject {current_time}"

    def subject_option_changed(self, event=None):
        """Handle subject option change."""
        selected_option = self.subject_var.get()
        self.configure["subject_mode"] = selected_option.lower().replace(" ", "_")
        
        if selected_option in ["Write My Own", "Auto Attach Name and Custom"]:
            self.subject_entry.place(x=100, y=50)
            self.subject_entry.configure(state='normal')
            self.text_subject_label.place_forget()
            self.text_subject_path = None
            self.configure["text_subject_path"] = None
            self.subjects = []
            self.update_log(f"Subject mode set to: {selected_option}")
        elif selected_option == "Attach subject From TXT File":
            self.subject_entry.place_forget()
            self.text_subject_label.place(x=10, y=80)
            self.app.after(100, self.attach_subject_file)
        elif selected_option in ["Attach Subject from CSV", "Auto Attach Name and CSV"]:
            self.subject_entry.place_forget()
            self.text_subject_label.place_forget()
            self.text_subject_path = None
            self.configure["text_subject_path"] = None
            self.subjects = []
            self.update_log(f"Subject mode set to: {selected_option}. Uses 'subject' column from recipient CSV.")
            self.gui_queue.put(lambda: messagebox.showinfo("Info", f"{selected_option} uses the 'subject' column from the recipient CSV file."))
        else:
            self.subject_entry.place_forget()
            self.text_subject_label.place_forget()
            self.text_subject_path = None
            self.configure["text_subject_path"] = None
            self.subjects = []
            self.update_log(f"Subject mode set to: {selected_option}")

    def attach_subject_file(self):
        """Attach subject file from TXT."""
        self.text_subject_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        try:
            if self.text_subject_path and os.path.exists(self.text_subject_path):
                self.subjects = []
                try:
                    with open(self.text_subject_path, 'r', encoding='utf-8') as file:
                        for line in file:
                            if line.strip():
                                self.subjects.append(line.strip())
                except UnicodeDecodeError:
                    with open(self.text_subject_path, 'r', encoding='latin-1') as file:
                        for line in file:
                            if line.strip():
                                self.subjects.append(line.strip())
                
                if self.subjects:
                    self.text_subject_label.configure(text=os.path.basename(self.text_subject_path))
                    self.configure["text_subject_path"] = self.text_subject_path
                    self.update_log(f"Text file attached: {os.path.basename(self.text_subject_path)}, {len(self.subjects)} subjects loaded.")
                    self.gui_queue.put(lambda: messagebox.showinfo("Success", f"Loaded {len(self.subjects)} subjects from {os.path.basename(self.text_subject_path)}"))
                else:
                    self.text_subject_label.configure(text="No valid subjects found")
                    self.configure["text_subject_path"] = None
                    self.subjects = []
                    self.update_log("Error: The subject file is empty or contains no valid subjects.")
                    self.gui_queue.put(lambda: messagebox.showerror("Error", "The subject file is empty or contains no valid subjects."))
            else:
                self.text_subject_label.configure(text="No file selected")
                self.configure["text_subject_path"] = None
                self.subjects = []
                self.update_log("No subject file selected.")
        except Exception as e:
            self.text_subject_label.configure(text="Error reading file")
            self.configure["text_subject_path"] = None
            self.subjects = []
            self.update_log(f"Error attaching subject file: {str(e)}")
            self.gui_queue.put(lambda: messagebox.showerror("Error", f"Failed to read subject file: {str(e)}"))

    def get_random_subject(self):
        """Get random subject from loaded subjects."""
        if not self.subjects:
            self.update_log("Error: No subjects available in text file.")
            return "No Subject"
        return random.choice(self.subjects)

    def pick_random_name(self):
        """Pick random sender name."""
        if self.random_name_var.get():
            self.sender_name_entry.delete(0, END)
            self.sender_name_entry.insert(0, random.choice(self.sender_names))
            self.update_log("Random sender name picked.")

    # ==================== EMAIL VALIDATION ====================
    
    def is_valid_email(self, email):
        """Enhanced email validation with comprehensive checks."""
        if not email:
            return None
        
        email = email.strip().lower()
        
        # Check length (RFC 5321)
        if len(email) > 254:
            return None
        
        # Check basic structure
        email_regex = r'^[a-zA-Z0-9.!#$%&\'*+/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$'
        if not re.match(email_regex, email):
            return None
        
        # Check for invalid patterns
        if '..' in email or '@@' in email or email.startswith('.') or email.endswith('.'):
            return None
        
        # Validate domain TLD
        parts = email.split('.')
        if len(parts[-1]) < 2:
            return None
        
        return email

    # ==================== RECIPIENT MANAGEMENT ====================
    
    def on_combobox_change(self, event):
        """Handle recipient mode change."""
        prev_mode = self.configure["send_mode"]
        self.update_email_fields(event)
        if self.actions_var.get() == "TEXT/CSV" and prev_mode != "send_from_file":
            self.app.after(100, self.attach_recipient_file)

    def update_email_fields(self, _=None):
        """Update email input fields based on mode."""
        raw_mode = self.actions_var.get().upper()
        send_mode = "send_manually" if raw_mode == "MANUAL" else "send_from_file"
        self.configure["send_mode"] = send_mode

        if send_mode == "send_manually":
            self.to_entry.configure(state='normal')
            self.to_entry.place(x=419, y=50)
            self.add_email_button.place(x=660, y=50)
            self.tester_recipient_textbox.place(x=419, y=90)
            self.recipient_textbox.place_forget()
            self.recipient_label.configure(text="")
            self.csv_file_path = None
            self.text_file_path = None
            self.configure["csv_file_path"] = None
            self.configure["text_file_path"] = None
        else:
            self.to_entry.configure(state='disabled')
            self.to_entry.place(x=419, y=50)
            self.add_email_button.place_forget()
            self.tester_recipient_textbox.place_forget()
            self.recipient_textbox.place(x=660, y=90)

    def attach_recipient_file(self, *_):
        """Attach recipient file (CSV or TXT)."""
        file_path = filedialog.askopenfilename(filetypes=[("Text or CSV files", "*.txt;*.csv")])
        if not file_path:
            self.recipient_label.configure(text="")
            self.update_log("No recipient file selected.")
            return
        
        if file_path.lower().endswith('.csv'):
            self.csv_file_path = file_path
            self.text_file_path = None
            self.configure["csv_file_path"] = file_path
            self.configure["text_file_path"] = None
            self.recipient_label.configure(text=os.path.basename(file_path))
            self.update_log("CSV file attached.")
            self.add_email_addresses_from_csv()
        elif file_path.lower().endswith('.txt'):
            self.text_file_path = file_path
            self.csv_file_path = None
            self.configure["text_file_path"] = file_path
            self.configure["csv_file_path"] = None
            self.recipient_label.configure(text=os.path.basename(file_path))
            self.update_log("Text file attached.")
            self.add_email_addresses_from_text()
        else:
            self.recipient_label.configure(text="")
            self.update_log("Invalid file type selected. Please choose a .txt or .csv file.")

    def add_email_addresses_from_csv(self):
        """Add email addresses from CSV file."""
        if self.csv_file_path:
            try:
                df = pd.read_csv(self.csv_file_path)
                df = self.normalize_csv_columns(df)
                
                if "email" not in df.columns:
                    self.update_log("Error: CSV file must contain an 'Email' column.")
                    messagebox.showerror("Error", "CSV file must contain an 'Email' column.")
                    return

                current_emails = set(self.recipient_textbox.get("1.0", END).strip().split("\n"))
                self.recipient_textbox.configure(state='normal')
                added_count = 0

                for email in df["email"].dropna().astype(str):
                    normalized_email = self.is_valid_email(email)
                    if normalized_email and normalized_email not in current_emails:
                        self.recipient_textbox.insert(END, normalized_email + "\n")
                        current_emails.add(normalized_email)
                        added_count += 1
                    elif email.strip():
                        self.update_log(f"Skipped email from CSV: {email} (invalid or duplicate)")

                self.recipient_textbox.configure(state='disabled')
                self.update_log(f"Added {added_count} new emails from CSV.")

            except Exception as e:
                self.update_log(f"Error reading CSV: {e}")
                messagebox.showerror("Error", f"Failed to read CSV file: {str(e)}")

    def add_email_addresses_from_text(self):
        """Add email addresses from text file."""
        if not self.text_file_path:
            messagebox.showwarning("No File", "No text file selected.")
            return

        try:
            self.recipient_textbox.configure(state=NORMAL)
            current_emails = set(email.strip() for email in self.recipient_textbox.get("1.0", END).splitlines() if email.strip())
            added_count = 0

            encodings = ['utf-8', 'latin-1', 'cp1252']
            success = False

            for encoding in encodings:
                try:
                    with open(self.text_file_path, 'r', encoding=encoding) as file:
                        for line in file:
                            email = line.strip()
                            normalized_email = self.is_valid_email(email)
                            if normalized_email and normalized_email not in current_emails:
                                self.recipient_textbox.insert(END, normalized_email + "\n")
                                current_emails.add(normalized_email)
                                added_count += 1
                    success = True
                    break
                except UnicodeDecodeError:
                    continue

            if not success:
                messagebox.showerror("Error", "Could not read the text file with any supported encoding.")
            else:
                if added_count > 0:
                    messagebox.showinfo("Success", f"Added {added_count} new email addresses.")
                else:
                    messagebox.showwarning("No New Emails", "No new valid email addresses found in the file.")

            self.recipient_textbox.configure(state=DISABLED)

        except Exception as e:
            messagebox.showerror("Error", f"Failed to read text file: {str(e)}")
            self.recipient_textbox.configure(state=DISABLED)

    def add_email(self, event=None):
        """Add email to manual recipient list."""
        if self.configure["send_mode"] == "send_manually":
            emails = self.to_entry.get().strip().split(',')
            current_emails = set(line.strip() for line in self.tester_recipient_textbox.get("1.0", END).splitlines() if line.strip())
            added_emails = False
            self.tester_recipient_textbox.configure(state='normal')

            for email in emails:
                normalized_email = self.is_valid_email(email)
                if normalized_email and normalized_email not in current_emails:
                    self.tester_recipient_textbox.insert(END, normalized_email + "\n")
                    current_emails.add(normalized_email)
                    self.update_log(f"Added tester email: {normalized_email}")
                    added_emails = True
                elif email.strip():
                    self.update_log(f"Skipped tester email: {email} (invalid or duplicate)")

            self.tester_recipient_textbox.configure(state='disabled')
            if added_emails:
                self.to_entry.delete(0, END)
            else:
                self.update_log("No valid or new tester emails added.")
                messagebox.showwarning("Warning", "Please enter valid email addresses or avoid duplicates.")
        else:
            self.update_log("Error: Email addition only allowed in 'Send Manually' mode.")

    def start_selection(self, event):
        """Start email selection."""
        textbox = event.widget
        textbox.configure(state='normal')
        index = textbox.index("@%d,%d" % (event.x, event.y))
        textbox.tag_remove("sel", "1.0", END)
        textbox.tag_add("sel", index, f"{index} lineend")
        self.update_selected_emails(textbox)
        textbox.configure(state='disabled')

    def extend_selection(self, event):
        """Extend email selection."""
        textbox = event.widget
        textbox.configure(state='normal')
        current_index = textbox.index("@%d,%d" % (event.x, event.y))
        textbox.tag_add("sel", "sel.first", f"{current_index} lineend")
        self.update_selected_emails(textbox)
        textbox.configure(state='disabled')

    def update_selected_emails(self, textbox):
        """Update selected emails set."""
        try:
            with self.selected_emails_lock:
                selected_text = textbox.get("sel.first", "sel.last").strip()
                if selected_text:
                    selected_emails = set(selected_text.split("\n"))
                    self.selected_emails.update(selected_emails)
                else:
                    self.selected_emails.clear()
        except tk.TclError:
            with self.selected_emails_lock:
                self.selected_emails.clear()

    def delete_selected_emails(self):
        """Delete selected emails."""
        current_mode = self.actions_combo.get()
        if not self.selected_emails:
            self.update_log("No emails selected for deletion.")
            messagebox.showwarning("Warning", "Please select emails to delete.")
            return

        if current_mode == "MANUAL":
            self.tester_recipient_textbox.configure(state="normal")
            current_emails = self.tester_recipient_textbox.get("1.0", END).strip().split("\n")
            remaining_emails = [email for email in current_emails if email and self.is_valid_email(email) not in self.selected_emails]
            self.tester_recipient_textbox.delete("1.0", END)
            for email in remaining_emails:
                self.tester_recipient_textbox.insert(END, email + "\n")
            self.tester_recipient_textbox.configure(state="disabled")
            self.update_log(f"Deleted {len(self.selected_emails)} manual emails.")
        elif current_mode == "TEXT/CSV":
            self.recipient_textbox.configure(state="normal")
            current_emails = self.recipient_textbox.get("1.0", END).strip().split("\n")
            remaining_emails = [email for email in current_emails if email and self.is_valid_email(email) not in self.selected_emails]
            self.recipient_textbox.delete("1.0", END)
            for email in remaining_emails:
                self.recipient_textbox.insert(END, email + "\n")
            self.recipient_textbox.configure(state="disabled")
            self.update_log(f"Deleted {len(self.selected_emails)} CSV/TEXT emails.")
        
        with self.selected_emails_lock:
            self.selected_emails.clear()

    def select_all_emails(self):
        """Select all emails in textboxes."""
        if self.select_all_var.get():
            try:
                self.tester_recipient_textbox.configure(state='normal')
                self.recipient_textbox.configure(state='normal')
                
                tester_emails = [line.strip() for line in self.tester_recipient_textbox.get("1.0", END).splitlines() if line.strip()]
                self.tester_recipient_textbox.tag_add("sel", "1.0", END)
                with self.selected_emails_lock:
                    self.selected_emails.update(tester_emails)
                
                recipient_emails = [line.strip() for line in self.recipient_textbox.get("1.0", END).splitlines() if line.strip()]
                self.recipient_textbox.tag_add("sel", "1.0", END)
                with self.selected_emails_lock:
                    self.selected_emails.update(recipient_emails)
                
                self.tester_recipient_textbox.configure(state='disabled')
                self.recipient_textbox.configure(state='disabled')
                self.update_log("All emails selected.")
            except Exception as e:
                self.update_log(f"Select all error: {str(e)}")
        else:
            self.tester_recipient_textbox.tag_remove("sel", "1.0", END)
            self.recipient_textbox.tag_remove("sel", "1.0", END)
            with self.selected_emails_lock:
                self.selected_emails.clear()
            self.update_log("Selection cleared.")

    def get_all_recipient(self):
        """Get all recipients based on current mode."""
        # NOTE: For tester/manual mode we DO NOT filter by self.sent_emails so
        # the tester box can re-send the same addresses multiple times.
        with self.sent_emails_lock:
            if self.configure["send_mode"] == "send_manually":
                emails = [line.strip() for line in self.tester_recipient_textbox.get("1.0", END).splitlines() if line.strip()]
                if not emails:
                    self.update_log("No emails in tester list.")
                    return []
                # Return ALL tester emails (no filtering) so test sends can repeat
                self.update_log(f"Retrieved {len(emails)} tester emails for manual mode")
                return [{"Email": email} for email in emails]
    
            elif self.configure["send_mode"] == "send_from_file":
                emails = [line.strip() for line in self.recipient_textbox.get("1.0", END).splitlines() if line.strip()]
                if not emails:
                    self.update_log("No emails in recipient list.")
                    return []
    
                filtered_emails = [email for email in emails if email not in self.sent_emails]
                if not filtered_emails:
                    self.update_log("No unsent emails remain in recipient list.")
                    return []
    
                self.update_log(f"Retrieved {len(filtered_emails)} unsent emails from recipient list (total: {len(emails)})")
    
                if self.csv_file_path and os.path.exists(self.csv_file_path):
                    try:
                        df = pd.read_csv(self.csv_file_path)
                        df = self.normalize_csv_columns(df)
    
                        if "email" not in df.columns:
                            self.update_log("Warning: CSV file missing 'Email' column, using recipient textbox data.")
                            return [{"Email": email} for email in filtered_emails]
    
                        filtered_df = df[df["email"].isin(filtered_emails)]
                        if filtered_df.empty:
                            self.update_log("Warning: No matching unsent emails found in CSV, using recipient textbox data.")
                            return [{"Email": email} for email in filtered_emails]
    
                        return filtered_df.to_dict('records')
                    except Exception as e:
                        self.update_log(f"Error processing CSV emails: {str(e)}")
                        self.update_log("Falling back to recipient textbox data.")
                        return [{"Email": email} for email in filtered_emails]
    
                return [{"Email": email} for email in filtered_emails]

    # ==================== SENDER MANAGEMENT ====================
    
    def update_api_smtp(self, event=None):
        """Update UI based on sending mode with auto-load."""
        send_mode = self.send_mode_var.get().lower().replace(" ", "_")
        self.configure["send_modes"] = send_mode
        self.attach_senders_button.place_forget()
        
        if send_mode == "multiple_smtp":
            # FIXED: Auto-load senders when switching to Multiple SMTP
            self.auto_load_senders_from_csv()
            
            self.sender_email_entry.place_forget()
            self.sender_password_entry.place_forget()
            
            # FIXED: Show loaded count on main UI
            loaded_count = len(self.sender_accounts)
            if loaded_count > 0:
                self.smtp_label.configure(text=f"✅ {loaded_count} senders loaded")
                self.smtp_label.place(x=10, y=470)
            else:
                self.smtp_label.configure(text="Click 'Attach Senders' to manage")
                self.smtp_label.place(x=10, y=470)
            
            self.attach_senders_button.place(x=286, y=470)
            self.app.after(100, self.open_sender_manager)
        elif send_mode == "gmail_api":
            self.sender_email_entry.place(x=100, y=120)
            self.sender_password_entry.place_forget()
            self.smtp_label.place_forget()
            self.app.after(100, self.authenticate_gmail)
        elif send_mode in ["icloud_smtp", "gmail_smtp"]:
            self.sender_email_entry.place(x=100, y=120)
            self.sender_password_entry.place(x=100, y=155)
            self.smtp_label.place_forget()
            self.update_log(f"Enter {'iCloud' if send_mode == 'icloud_smtp' else 'Gmail'} email and app-specific password.")

    def authenticate_gmail(self):
        """Authenticate Gmail API."""
        self.oauth_provider = 'gmail'
        self.gmail_credentials_path = filedialog.askopenfilename(filetypes=[("JSON files", "*.json")])
        self.configure["authenticate_gmail"] = self.gmail_credentials_path
        
        if self.gmail_credentials_path:
            self.update_log(f"Gmail credentials file attached: {os.path.basename(self.gmail_credentials_path)}")
            self.gui_queue.put(lambda: messagebox.showinfo("Success", "Gmail OAuth 2.0 credentials selected."))
        else:
            self.update_log("Error: No file selected for Gmail OAuth.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", "No file selected for Gmail OAuth 2.0 authentication."))
            self.configure["authenticate_gmail"] = None

    def remove_sender_csv_file(self):
        """Remove sender CSV file."""
        self.sender_csv_file_path = None
        self.smtp_label.configure(text="")
        self.remove_smtp_button.place_forget()
        self.configure["sender_csv_file_path"] = None
        with self.sender_accounts_lock:
            self.sender_accounts = []
        self.update_log("Sender CSV file removed.")

    def handle_sender_failure_and_replace(self, sender_email):
        """NEW: Move failed sender to failed list and activate replacement if available."""
        with self.sender_accounts_lock:
            # Find and remove failed sender
            failed_sender = next((s for s in self.sender_accounts if s["email"] == sender_email), None)
            if failed_sender:
                self.sender_accounts.remove(failed_sender)
                self.failed_senders.append(failed_sender)
                self.update_log(f"Moved {sender_email} to failed senders")
                
                # Update GUI row status
                def update_status():
                    for row in self.sender_rows:
                        if row["entries"]["email"].get() == sender_email:
                            row["entries"]["status_label"].configure(text="Failed", text_color="red")
                            break
                self.gui_queue.put(update_status)
                
                # Try to activate replacement sender
                if self.replacement_senders:
                    replacement = self.replacement_senders.pop(0)
                    self.sender_accounts.append(replacement)
                    self.update_log(f"Activated replacement sender: {replacement['email']}")
                    
                    # Get remaining recipients from failed sender
                    if sender_email in self.sender_recipient_lists:
                        remaining = self.sender_recipient_lists[sender_email]
                        self.sender_recipient_lists[replacement["email"]] = remaining
                        del self.sender_recipient_lists[sender_email]
                        
                        # Start new worker thread for replacement
                        threading.Thread(
                            target=self._send_worker, 
                            args=(replacement, remaining, None),
                            daemon=True
                        ).start()
                        
                    messagebox.showinfo("Sender Replaced", 
                        f"Failed sender {sender_email} replaced with {replacement['email']}")
                else:
                    self.update_log("No replacement senders available")
                    messagebox.showwarning("No Replacements", 
                        f"Sender {sender_email} failed with no replacements available")

    def validate_smtp_presets(self):
        """Validate SMTP presets are properly configured."""
        print("\n=== SMTP PRESETS VALIDATION ===")
        for key, preset in SMTP_PRESETS.items():
            host = preset.get('host', '')
            port = preset.get('port', 0)
            status = "✅" if host and port else "❌"
            print(f"{status} {key:15} -> {host:30} : {port}")
        print("================================\n")


        # ==================== EMAIL SENDING CORE METHODS ====================
    
    def _send_worker(self, sender, recipients_per_sender=None, smtp_conn=None):
        
        if recipients_per_sender is None:
            raise ValueError("recipients_per_sender must be provided")
    
        sender_email = sender["email"]
        s_type = sender.get("type", "smtp")
        sender_sent_count = 0
        sender_failed_count = 0
        smtp_conn_local = smtp_conn
    
        # -------- Batch Limit ----------------------------------------------------
        try:
            batch_limit = int(self.emails_per_batch.get().strip() or 0)
        except Exception:
            batch_limit = 0
        if batch_limit > 0:
            recipients_per_sender = recipients_per_sender[:batch_limit]
            self.update_log(f"Batch limit applied: sending only first {batch_limit} emails for {sender_email}")
    
        # -------- Optional initial delay ----------------------------------------
        if self.random_pause_var.get():
            delay = random.uniform(PAUSE_MIN, PAUSE_MAX)
            self.update_log(f"Initial delay {delay:.1f}s for {sender_email}")
            time.sleep(delay)
    
        # -------- Main loop ------------------------------------------------------
        try:
            for recipient in recipients_per_sender:
                if self.stop_event.is_set():
                    break
    
                # Pause handling
                while self.pause_event.is_set() and not self.stop_event.is_set():
                    time.sleep(0.3)
    
                # Extract recipient email
                if isinstance(recipient, dict):
                    recipient_email = recipient.get("Email", recipient.get("email", "")).strip()
                else:
                    recipient_email = str(recipient).strip()
                if not recipient_email:
                    continue
    
                send_mode = self.configure.get("send_mode")
    
                # Skip already-sent only for CSV/TEXT mode
                if send_mode == "send_from_file":
                    with self.sent_emails_lock:
                        if recipient_email in self.sent_emails:
                            continue
    
                # Rate-limit
                try:
                    self.check_rate_limit(sender_email)
                except Exception:
                    pass
    
                # -------- Try sending --------------------------------------------
                success = False
                last_error = ""
                for attempt in range(3):
                    try:
                        ok = self.send_single_email(sender, recipient_email, smtp_conn_local)
                        if ok:
                            success = True
                            break
                    except Exception as e:
                        last_error = str(e)
                        self.update_log(f"Retry {attempt + 1} failed for {recipient_email} ({sender_email}): {last_error}")
                        time.sleep(1.5)
                        continue
    
                ts = datetime.now().isoformat()
                with self.sender_logs_lock:
                    self.sender_logs.setdefault(sender_email, []).append(
                        (recipient_email, success, last_error if not success else "", ts)
                    )
    
                # -------- Counters / Deletion / GUI ------------------------------
                if success:
                    sender_sent_count += 1
                    with self.emails_sent_lock:
                        self.emails_sent += 1
    
                    # Mark as sent & delete only for CSV mode
                    if send_mode == "send_from_file":
                        with self.sent_emails_lock:
                            self.sent_emails.add(recipient_email)
    
                        # Deletion from textbox on GUI thread
                        def _remove_sent_recipient():
                            try:
                                tb = self.recipient_textbox
                                tb.configure(state='normal')
                                text_data = tb.get("1.0", tk.END).splitlines()
                                new_lines = []
                                removed = False
                                for line in text_data:
                                    clean = line.strip()
                                    if clean and clean != recipient_email:
                                        new_lines.append(clean)
                                    elif clean == recipient_email:
                                        removed = True
                                tb.delete("1.0", tk.END)
                                for l in new_lines:
                                    tb.insert(tk.END, l + "\n")
                                tb.configure(state='disabled')
                                if removed:
                                    self.update_log(f"🧹 Removed sent recipient: {recipient_email}")
                            except Exception as e:
                                self.update_log(f"Error updating Recipient textbox: {e}")
    
                        self.gui_queue.put(_remove_sent_recipient)
    
                else:
                    sender_failed_count += 1
                    self.update_log(f"❌ Failed to send {recipient_email} from {sender_email}: {last_error}")
    
                # Refresh log & progress once per recipient
                self.gui_queue.put(self.update_log_display)
                self.gui_queue.put(lambda: self.progress_label.configure(
                    text=f"Progress: {self.emails_sent} / {self.total_emails}"))
                self.gui_queue.put(lambda: self.progress_bar.set(
                    self.emails_sent / max(1, self.total_emails)))
    
                # -------- Auto/Normal pause --------------------------------------
                if self.auto_pause_var.get() and sender_sent_count % int(self.auto_pause_count.get() or 100) == 0:
                    self.update_log(f"Auto-pause 3 s after {sender_sent_count} emails by {sender_email}")
                    time.sleep(3)
    
                if not self.stop_event.is_set():
                    wait_time = random.uniform(PAUSE_MIN, PAUSE_MAX) if self.random_pause_var.get() else float(self.timer_entry.get() or 5)
                    time.sleep(wait_time)
    
        except Exception as e:
            self.update_log(f"Worker error for {sender_email}: {str(e)}")
    
        finally:
            try:
                if smtp_conn_local:
                    smtp_conn_local.quit()
            except Exception:
                pass
    
        self.update_log(f"✅ Worker finished for {sender_email}: Sent={sender_sent_count}, Failed={sender_failed_count}")
    
    def send_single_email(self, sender, recipient, smtp_conn=None):
        """Send a single email using the specified sender."""
        try:
            subject = self.get_subject("", "", row=None)
            msg = self.compose_email(
                to_email=recipient, 
                from_email=sender["email"],
                subject=subject, 
                name="", 
                last_name="", 
                customer_id=None, 
                membership_id=None
            )
            
            s_type = sender.get("type", "smtp")
            self.update_log(f"Preparing to send to {recipient} via {s_type} from {sender['email']}")
            
            timestamp = datetime.now().isoformat()
            
            if s_type == "gmail_api":
                # Gmail API sending
                email_safe = re.sub(r'[^a-zA-Z0-9_]', '_', sender["email"])
                token_file = f'token_{email_safe}.json'
                creds = None
                
                if os.path.exists(token_file):
                    creds = Credentials.from_authorized_user_file(token_file, GMAIL_SCOPES)
                
                if not creds or not creds.valid:
                    if creds and creds.expired and creds.refresh_token:
                        creds.refresh(Request())
                    else:
                        cred_path = sender.get("credentials") or self.gmail_credentials_path
                        if not cred_path or not os.path.exists(cred_path):
                            self.update_log(f"Gmail API credentials not found for {sender['email']}.")
                            with self.sender_logs_lock:
                                self.sender_logs.setdefault(sender['email'], []).append(
                                    (recipient, False, "Missing credentials", timestamp))
                            raise ValueError("Missing credentials")
                        
                        flow = InstalledAppFlow.from_client_secrets_file(cred_path, GMAIL_SCOPES)
                        creds = flow.run_local_server(port=0)
                    
                    with open(token_file, 'w') as token:
                        token.write(creds.to_json())
                
                service = build("gmail", "v1", credentials=creds)
                raw = base64.urlsafe_b64encode(msg.as_bytes()).decode()
                service.users().messages().send(userId="me", body={"raw": raw}).execute()
                
                self.update_log(f"Sent via Gmail API: {recipient} from {sender['email']}")
                with self.sent_emails_lock:
                    self.sent_emails.add(recipient)
                with self.sender_logs_lock:
                    self.sender_logs.setdefault(sender['email'], []).append((recipient, True, "", timestamp))
                self.gui_queue.put(self.update_log_display)
                return True
            
            # SMTP sending
            host = sender.get("host") or SMTP_PRESETS.get(s_type, {}).get('host', '')
            port = sender.get("port") or SMTP_PRESETS.get(s_type, {}).get('port', 587)
            password = sender.get("password", "")
            
            if smtp_conn is None or not self._is_smtp_connection_valid(smtp_conn, sender["email"]):
                if port == 465:
                    smtp_conn = smtplib.SMTP_SSL(host, port, timeout=30)
                else:
                    smtp_conn = smtplib.SMTP(host, port, timeout=30)
                    smtp_conn.starttls()
                smtp_conn.login(sender["email"], password)
            
            smtp_conn.sendmail(sender["email"], recipient, msg.as_string())
            self.update_log(f"Sent via SMTP: {recipient} from {sender['email']}")
            
            with self.sent_emails_lock:
                self.sent_emails.add(recipient)
            with self.sender_logs_lock:
                self.sender_logs.setdefault(sender['email'], []).append((recipient, True, "", timestamp))
            self.gui_queue.put(self.update_log_display)
            return True
            
        except Exception as e:
            self.update_log(f"Send failed for {sender['email']} -> {recipient}: {str(e)}")
            with self.sender_logs_lock:
                self.sender_logs.setdefault(sender['email'], []).append((recipient, False, str(e), timestamp))
            self.gui_queue.put(self.update_log_display)
            raise

    def _is_smtp_connection_valid(self, smtp_conn, sender_email):
        """Check if SMTP connection is valid."""
        if smtp_conn is None:
            return False
        try:
            status = smtp_conn.noop()[0]
            return status == 250
        except smtplib.SMTPException as e:
            self.update_log(f"SMTP connection invalid for {sender_email}: {str(e)}")
            return False

    def auto_load_senders_from_csv(self):
        """Auto-load senders from CSV with auto-fill for missing host/port."""
        loaded_main = 0
        loaded_repl = 0
        loaded_failed = 0
        
        # Load main senders
        if os.path.exists('senders_main.csv'):
            try:
                df = pd.read_csv('senders_main.csv')
                df = self.normalize_csv_columns(df)
                
                senders_data = df.to_dict('records')
                
                # FIXED: Auto-fill missing host/port from presets
                for sender in senders_data:
                    s_type = sender.get('type', 'smtp')
                    if not sender.get('host') or not sender.get('port'):
                        preset = SMTP_PRESETS.get(s_type, {})
                        if not sender.get('host'):
                            sender['host'] = preset.get('host', '')
                        if not sender.get('port'):
                            sender['port'] = preset.get('port', 587)
                        self.update_log(f"Auto-filled {sender['email']} ({s_type}): {sender['host']}:{sender['port']}")
                
                with self.sender_accounts_lock:
                    self.sender_accounts = senders_data
                    loaded_main = len(self.sender_accounts)
                
                self.update_log(f"Auto-loaded {loaded_main} main senders from senders_main.csv")
            except Exception as e:
                self.update_log(f"Error loading senders_main.csv: {str(e)}")
        
        # Load replacement senders
        if os.path.exists('senders_replacement.csv'):
            try:
                df = pd.read_csv('senders_replacement.csv')
                df = self.normalize_csv_columns(df)
                
                senders_data = df.to_dict('records')
                
                # Auto-fill missing host/port
                for sender in senders_data:
                    s_type = sender.get('type', 'smtp')
                    if not sender.get('host') or not sender.get('port'):
                        preset = SMTP_PRESETS.get(s_type, {})
                        if not sender.get('host'):
                            sender['host'] = preset.get('host', '')
                        if not sender.get('port'):
                            sender['port'] = preset.get('port', 587)
                
                with self.sender_accounts_lock:
                    self.replacement_senders = senders_data
                    loaded_repl = len(self.replacement_senders)
                
                self.update_log(f"Auto-loaded {loaded_repl} replacement senders from senders_replacement.csv")
            except Exception as e:
                self.update_log(f"Error loading senders_replacement.csv: {str(e)}")
        
        # Load failed senders
        if os.path.exists('senders_failed.csv'):
            try:
                df = pd.read_csv('senders_failed.csv')
                df = self.normalize_csv_columns(df)
                
                with self.sender_accounts_lock:
                    self.failed_senders = df.to_dict('records')
                    loaded_failed = len(self.failed_senders)
                
                self.update_log(f"Auto-loaded {loaded_failed} failed senders from senders_failed.csv")
            except Exception as e:
                self.update_log(f"Error loading senders_failed.csv: {str(e)}")
        
        total_loaded = loaded_main + loaded_repl + loaded_failed
        if total_loaded > 0:
            self.update_log(f"✅ Total auto-loaded: {total_loaded} senders (Main: {loaded_main}, Repl: {loaded_repl}, Failed: {loaded_failed})")
            self.refresh_test_sender_combo()
        else:
            self.update_log("No existing sender CSV files found. Start fresh or import CSV.")

    def start_send_thread(self):
        """Start the email sending thread with EXTENSIVE debugging."""
        body = self.body_textbox.get("1.0", tk.END).strip()
        html = self.html_textbox.get("1.0", tk.END).strip() if self.html_var.get() else ""
        
        if not body and not html:
            messagebox.showerror("Error", "Please enter content in the body or HTML field.")
            return
        
        recipients = self.get_all_recipient()
        if not recipients:
            messagebox.showerror("Error", "No recipients found in the selected list.")
            return
        
        if self.sending_thread and self.sending_thread.is_alive():
            self.stop_sending()
            return
        
        # Disable UI controls
        self.disable_ui_controls()
        
        self.send_button.configure(text="Stop Sending", fg_color="red", command=self.stop_sending)
        self.stop_button.place(x=730, y=590)
        
        send_mode = self.send_mode_var.get().lower().replace(" ", "_")
        
        if send_mode != "multiple_smtp":
            self.stop_event.clear()
            with self.emails_sent_lock:
                self.emails_sent = 0
            self.total_emails = len(recipients)
            self.progress_label.configure(text=f"Progress: {self.emails_sent} / {self.total_emails}")
            self.progress_bar.set(0)
            self.sending_thread = threading.Thread(target=self.send_emails, args=(recipients,), daemon=True)
            self.sending_thread.start()
            return
        
        # ========== MULTIPLE SMTP MODE - ENHANCED VALIDATION ==========
        
        print("\n" + "="*60)
        print("SEND EMAIL BUTTON - VALIDATION START")
        print("="*60)
        
        with self.sending_lock:
            # Check if senders are loaded
            print(f"[CHECK 1] Senders in memory: {len(self.sender_accounts)}")
            
            if not self.sender_accounts and not self.replacement_senders:
                self.update_log("Error: No senders loaded. Opening Sender Manager...")
                self.enable_ui_controls()
                self.send_button.configure(text="Send Email", fg_color="blue", command=self.start_send_thread)
                self.stop_button.place_forget()
                messagebox.showerror("No Senders", 
                    "No sender accounts found!\n\n"
                    "Please:\n"
                    "1. Click 'Attach Senders' button\n"
                    "2. Add senders using 'Bulk Add' or 'Import CSV'\n"
                    "3. Click 'Save' to save senders\n"
                    "4. Try sending again"
                )
                self.open_sender_manager()
                return
            
            num_senders = len(self.sender_accounts)
            self.update_log(f"Found {num_senders} sender accounts in memory")
            
            # DEBUG: Print ALL sender data
            print(f"\n[CHECK 2] Detailed sender inspection:")
            for idx, sender in enumerate(self.sender_accounts, 1):
                print(f"\n  Sender #{idx}:")
                print(f"    Email: {sender.get('email', 'MISSING')}")
                print(f"    Type: {sender.get('type', 'MISSING')}")
                print(f"    Host: '{sender.get('host', 'MISSING')}' (len={len(sender.get('host', ''))})")
                print(f"    Port: {sender.get('port', 'MISSING')}")
                print(f"    Has Password: {bool(sender.get('password'))}")
            
            valid_senders = []
            smtp_conns = {}
            self.failed_senders = []
            validation_errors = []
            
            for sender in self.sender_accounts:
                s_type = sender.get("type", "smtp")
                sender_email = sender.get("email", "NO_EMAIL")
                
                print(f"\n[CHECK 3] Validating: {sender_email}")
                
                if s_type in ["smtp", "gmail_smtp", "icloud_smtp", "gmail", "att", "yahoo", "aol", "outlook", "zoho", "custom"]:
                    # Get host/port
                    host = sender.get("host")
                    port = sender.get("port")
                    
                    print(f"  Raw host: '{host}' (type: {type(host).__name__})")
                    print(f"  Raw port: {port} (type: {type(port).__name__})")
                    
                    # CRITICAL FIX: Handle different data types
                    if isinstance(host, str):
                        host = host.strip()
                    else:
                        host = str(host) if host else ""
                    
                    if not host:
                        # Try to get from presets
                        preset = SMTP_PRESETS.get(s_type, {})
                        host = preset.get('host', '')
                        port = preset.get('port', 587)
                        print(f"  Auto-filled from preset: host={host}, port={port}")
                        
                        # Update sender dict
                        sender['host'] = host
                        sender['port'] = port
                    
                    # Convert port to int
                    try:
                        port = int(port) if port else 587
                    except (ValueError, TypeError):
                        port = 587
                    
                    sender['port'] = port  # Ensure port is int
                    
                    print(f"  Final host: '{host}'")
                    print(f"  Final port: {port}")
                    
                    # Validate
                    if not host:
                        error = f"{sender_email}: Missing SMTP host (type: {s_type})"
                        print(f"  ❌ VALIDATION FAILED: {error}")
                        validation_errors.append(error)
                        self.failed_senders.append(sender)
                        continue
                    
                    # Try to connect
                    try:
                        print(f"  Attempting connection to {host}:{port}...")
                        
                        if port == 465:
                            smtp_conn = smtplib.SMTP_SSL(host, port, timeout=30)
                            print(f"  Connected via SSL")
                        else:
                            smtp_conn = smtplib.SMTP(host, port, timeout=30)
                            smtp_conn.starttls()
                            print(f"  Connected via TLS")
                        
                        smtp_conn.login(sender["email"], sender.get("password", ""))
                        smtp_conns[sender_email] = smtp_conn
                        valid_senders.append(sender)
                        print(f"  ✅ Validation PASSED")
                        self.update_log(f"✅ Validated SMTP connection for {sender_email}")
                        
                    except smtplib.SMTPException as e:
                        error = f"{sender_email}: {str(e)}"
                        print(f"  ❌ Connection FAILED: {str(e)}")
                        validation_errors.append(error)
                        self.update_log(f"❌ Login failed for {sender_email}: {str(e)}")
                        self.failed_senders.append(sender)
                        continue
                        
                elif s_type == "gmail_api":
                    cred_path = sender.get("credentials") or self.gmail_credentials_path
                    if not cred_path or not os.path.exists(cred_path):
                        error = f"{sender_email}: Gmail API credentials not found"
                        print(f"  ❌ {error}")
                        validation_errors.append(error)
                        self.failed_senders.append(sender)
                        continue
                    valid_senders.append(sender)
                    print(f"  ✅ Gmail API validation passed")
                else:
                    error = f"{sender_email}: Unknown type '{s_type}'"
                    print(f"  ❌ {error}")
                    validation_errors.append(error)
                    self.failed_senders.append(sender)
                    continue
            
            print(f"\n[CHECK 4] Validation Summary:")
            print(f"  Total loaded: {num_senders}")
            print(f"  Valid: {len(valid_senders)}")
            print(f"  Failed: {len(self.failed_senders)}")
            print("="*60 + "\n")
            
            if not valid_senders:
                self.update_log("Error: No valid sender accounts after validation.")
                self.enable_ui_controls()
                self.send_button.configure(text="Send Email", fg_color="blue", command=self.start_send_thread)
                self.stop_button.place_forget()
                
                # Build detailed error message
                error_msg = f"❌ No valid sender accounts available!\n\n"
                error_msg += f"Total senders loaded: {num_senders}\n"
                error_msg += f"Failed validation: {len(self.failed_senders)}\n\n"
                error_msg += "Common issues:\n"
                error_msg += "• Wrong email/password\n"
                error_msg += "• Missing SMTP host/port\n"
                error_msg += "• App-specific password required\n"
                error_msg += "• Firewall blocking connection\n\n"
                
                if validation_errors:
                    error_msg += "Detailed errors:\n"
                    for err in validation_errors[:5]:  # Show first 5
                        error_msg += f"  - {err}\n"
                
                if self.failed_senders:
                    error_msg += f"\nFailed senders:\n"
                    for s in self.failed_senders[:5]:
                        error_msg += f"  - {s['email']} ({s.get('type', 'smtp')})\n"
                        error_msg += f"    Host: '{s.get('host', 'EMPTY')}'\n"
                        error_msg += f"    Port: {s.get('port', 'EMPTY')}\n"
                
                messagebox.showerror("Validation Failed", error_msg)
                return
            
            num_valid_senders = len(valid_senders)
            with self.sender_accounts_lock:
                self.sender_accounts = valid_senders
            
            confirm = messagebox.askyesno("Confirm Send",
                f"✉️ Ready to send!\n\n"
                f"Recipients: {len(recipients)}\n"
                f"Valid senders: {num_valid_senders}\n"
                f"Failed senders: {len(self.failed_senders)}\n"
                f"Threads: Up to {self.max_concurrent_threads}\n\n"
                f"Continue?"
            )
            
            if not confirm:
                self.update_log("Email sending cancelled by user.")
                self.enable_ui_controls()
                self.send_button.configure(text="Send Email", fg_color="blue", command=self.start_send_thread)
                self.stop_button.place_forget()
                return
            
            self.stop_event.clear()
            self.send_button.configure(state='disabled')
            
            with self.emails_sent_lock:
                self.emails_sent = 0
            self.total_emails = len(recipients)
            self.progress_label.configure(text=f"Progress: {self.emails_sent} / {self.total_emails}")
            self.progress_bar.set(0)
            
            def send_emails_thread():
                # Distribute recipients among senders
                recipients_per_sender = [[] for _ in range(num_valid_senders)]
                for i, recipient in enumerate(recipients):
                    recipients_per_sender[i % num_valid_senders].append(recipient)
                
                with self.sender_accounts_lock:
                    self.sender_recipient_lists = {
                        s["email"]: list(rps) for s, rps in zip(self.sender_accounts, recipients_per_sender)
                    }
                
                # Log distribution
                for sender, recips in self.sender_recipient_lists.items():
                    self.update_log(f"Assigned {len(recips)} recipients to {sender}")
                
                # Start worker threads
                with ThreadPoolExecutor(max_workers=self.max_concurrent_threads) as executor:
                    futures = []
                    for i, sender in enumerate(self.sender_accounts):
                        sender_email = sender["email"]
                        s_type = sender.get("type", "smtp")
                        smtp_conn = smtp_conns.get(sender_email) if s_type in ["smtp", "gmail_smtp", "icloud_smtp"] else None
                        
                        future = executor.submit(self._send_worker, sender, recipients_per_sender[i], smtp_conn)
                        futures.append(future)
                    
                    for future in as_completed(futures):
                        if self.stop_event.is_set():
                            self.update_log("Sending stopped by user.")
                            break
                        try:
                            future.result()
                        except Exception as e:
                            self.update_log(f"Thread error: {str(e)}")
                    
                    # Close all SMTP connections
                    for sender_email, conn in smtp_conns.items():
                        try:
                            conn.quit()
                            self.update_log(f"Closed SMTP connection for {sender_email}")
                        except Exception as e:
                            self.update_log(f"Error closing SMTP connection for {sender_email}: {e}")
                
                # Re-enable UI
                self.gui_queue.put(lambda: self.enable_ui_controls())
                self.gui_queue.put(lambda: self.send_button.configure(
                    text="Send Email", fg_color="blue", command=self.start_send_thread, state='normal'))
                self.gui_queue.put(lambda: self.stop_button.place_forget())
                
                if self.emails_sent >= self.total_emails and not self.stop_event.is_set():
                    self.gui_queue.put(self.show_completion_popup)
                
                self.update_log("Multi-sender send finished.")
            
            self.sending_thread = threading.Thread(target=send_emails_thread, daemon=True)
            self.sending_thread.start()

    def disable_ui_controls(self):
        """Disable input fields during sending."""
        controls = [
            self.subject_entry, self.sender_name_entry, self.sender_email_entry, 
            self.sender_password_entry, self.body_textbox, self.html_textbox, 
            self.to_entry, self.emails_per_batch, self.timer_entry,
            self.actions_combo, self.send_mode_combo, self.attach_button, 
            self.add_email_button
        ]
        for control in controls:
            try:
                control.configure(state=DISABLED)
            except:
                pass

    def enable_ui_controls(self):
        """Re-enable input fields after sending."""
        controls = [
            self.subject_entry, self.sender_name_entry, self.sender_email_entry, 
            self.sender_password_entry, self.body_textbox, self.html_textbox, 
            self.to_entry, self.emails_per_batch, self.timer_entry,
            self.actions_combo, self.send_mode_combo, self.attach_button, 
            self.add_email_button
        ]
        for control in controls:
            try:
                control.configure(state=NORMAL)
            except:
                pass

    def test_send_from_selected(self):
        """Send test email from selected sender (upgraded)."""
        sel = self.test_sender_var.get()
        if not sel:
            messagebox.showwarning("Select Sender", "Please select a sender first.")
            return
    
        with self.sender_accounts_lock:
            sender = next((s for s in self.sender_accounts if s["email"] == sel), None)
        if not sender:
            messagebox.showerror("Error", f"Sender {sel} not found.")
            return
    
        recipients = [line.strip() for line in self.tester_recipient_textbox.get("1.0", tk.END).splitlines() if line.strip()]
        if not recipients:
            messagebox.showerror("Error", "Add tester recipients first.")
            return
    
        if not messagebox.askyesno("Confirm Test Send", f"Send {len(recipients)} test emails using {sel}?"):
            return
    
        # Allow same recipients multiple times
        with self.sent_emails_lock:
            self.sent_emails.clear()
    
        def test_send_thread():
            self.stop_event.clear()
            for recipient in recipients:
                try:
                    self.send_single_email(sender, recipient)
                    self.update_log(f"✅ Test sent to {recipient}")
                    time.sleep(1)
                except Exception as e:
                    self.update_log(f"❌ Test send failed for {recipient}: {str(e)}")
                    continue
            messagebox.showinfo("Done", "Test sending complete.")
            self.update_log("Test sending complete.")
    
        threading.Thread(target=test_send_thread, daemon=True).start()
        
        def test_send_thread():
            if self.stop_event.is_set():
                self.update_log("Test sending stopped before starting.")
                return
            
            recipient_emails = []
            for recipient in recipients:
                if isinstance(recipient, dict):
                    recipient_emails.append(recipient.get("Email", recipient.get("email", "")))
                else:
                    recipient_emails.append(recipient)
            
            try:
                self._send_worker(sender, recipient_emails, None)
            except Exception as e:
                self.update_log(f"Error in test send: {str(e)}")
            
            self.gui_queue.put(lambda: self.send_button.configure(state='normal'))
            
            if self.emails_sent >= self.total_emails and not self.stop_event.is_set():
                self.gui_queue.put(self.show_completion_popup)
            
            self.update_log("Test send finished.")
        
        threading.Thread(target=test_send_thread, daemon=True).start()

    def stop_sending(self):
        """Stop email sending."""
        self.stop_event.set()
        self.update_log("Stopping email sending...")
        self.enable_ui_controls()
        self.stop_button.place_forget()
        self.send_button.configure(text="Send Email", fg_color="blue", 
                                   command=self.start_send_thread, state=NORMAL)

    def toggle_pause(self):
        """Toggle pause state."""
        if self.pause_event.is_set():
            self.pause_event.clear()
            self.update_log("Email sending resumed.")
            def update_ui():
                self.pause_button.configure(text="Pause Sending", fg_color="#1A8B53")
                self.status_label.configure(text="Status: Sending")
            self.gui_queue.put(update_ui)
        else:
            self.pause_event.set()
            self.update_log("Email sending paused.")
            def update_ui():
                self.pause_button.configure(text="Resume Sending", fg_color="orange")
                self.status_label.configure(text="Status: Paused")
            self.gui_queue.put(update_ui)

    def send_emails(self, recipients):
        """Send emails in single sender mode."""
        try:
            with self.sending_lock:
                self.emails_sent = 0
                self.total_emails = len(recipients)
            
            self.update_progress(0, self.total_emails)
            send_mode = self.send_mode_var.get().lower().replace(" ", "_")
            
            if send_mode == "multiple_smtp":
                self.send_multiple_smtp_emails(recipients)
            elif send_mode == "gmail_api":
                self.send_api_emails(recipients)
            elif send_mode == "icloud_smtp":
                self.send_icloud_smtp_emails(recipients)
            elif send_mode == "gmail_smtp":
                self.send_gmail_smtp_emails(recipients)
            else:
                self.update_log(f"Unknown send mode: {send_mode}")
                self.gui_queue.put(lambda: messagebox.showerror("Error", f"Unknown send mode: {send_mode}"))
        
        except Exception as e:
            self.update_log(f"Error in send_emails: {str(e)}")
            self.gui_queue.put(lambda: messagebox.showerror("Error", f"Error during email sending: {str(e)}"))
        
        finally:
            self.gui_queue.put(lambda: self.send_button.configure(state=NORMAL))
            self.gui_queue.put(lambda: self.stop_button.place_forget())
            self.update_log("Email sending process completed.")
            
            if self.emails_sent > 0:
                self.gui_queue.put(lambda: messagebox.showinfo("Success", 
                    f"Sent {self.emails_sent} emails successfully."))
            
            self.sending_thread = None
            self.stop_event.clear()

    def send_multiple_smtp_emails(self, recipients):
        """Send using multiple SMTP accounts (legacy single-thread mode)."""
        if not self.sender_csv_file_path:
            self.update_log("Error: No sender CSV file attached.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", "No sender CSV file attached."))
            return
        
        try:
            df = pd.read_csv(self.sender_csv_file_path)
            df = self.normalize_csv_columns(df)
            senders = df.to_dict('records')
            
            if not all('email' in s for s in senders):
                self.update_log("Error: Sender CSV must include 'Email' column.")
                self.gui_queue.put(lambda: messagebox.showerror("Error", 
                    "Sender CSV must include 'Email' column."))
                return
        
        except Exception as e:
            self.update_log(f"Error reading sender CSV: {str(e)}")
            self.gui_queue.put(lambda: messagebox.showerror("Error", 
                f"Failed to read sender CSV: {str(e)}"))
            return
        
        sender_index = 0
        server = None
        current_sender = None
        emails_per_connection = 500
        
        try:
            for index, recipient in enumerate(recipients):
                if self.stop_event.is_set():
                    self.update_log("Email sending stopped.")
                    break
                
                sender = senders[sender_index % len(senders)]
                
                if server is None or current_sender != sender or (index % emails_per_connection == 0):
                    if server:
                        try:
                            server.quit()
                        except:
                            pass
                    
                    try:
                        server = smtplib.SMTP(sender["host"], int(sender["port"]))
                        server.starttls()
                        server.login(sender["email"], sender["password"])
                        current_sender = sender
                    except smtplib.SMTPException as e:
                        self.update_log(f"SMTP login error for {sender['email']}: {str(e)}")
                        self.stop_event.set()
                        return
                
                try:
                    self.process_emails([recipient], sender["email"], server=server)
                    
                    if isinstance(recipient, dict):
                        email = recipient.get("Email", recipient.get("email", ""))
                    else:
                        email = recipient
                    
                    if email in self.sent_emails:
                        if (index + 1) % emails_per_connection == 0:
                            sender_index = (sender_index + 1) % len(senders)
                
                except smtplib.SMTPException as e:
                    self.update_log(f"SMTP error for {sender['email']}: {str(e)}")
                    server = None
                    sender_index = (sender_index + 1) % len(senders)
                    continue
        
        finally:
            if server:
                try:
                    server.quit()
                except:
                    pass

    def send_api_emails(self, recipients):
        """Send using Gmail API."""
        if not self.gmail_credentials_path:
            self.update_log("Error: No Gmail credentials provided.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", "No Gmail credentials provided."))
            return
        
        from_email = self.sender_email_entry.get()
        if not from_email:
            self.update_log("Error: Sender email is required for API mode.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", 
                "Sender email is required for API mode."))
            return
        
        batch_size = int(self.emails_per_batch.get().strip() or len(recipients))
        recipients = recipients[:batch_size]
        
        self.update_log("Note: For custom sender names in Gmail API, configure aliases in Gmail settings.")
        
        creds = None
        try:
            if os.path.exists('token.json'):
                try:
                    creds = Credentials.from_authorized_user_file('token.json', GMAIL_SCOPES)
                except Exception as e:
                    self.update_log(f"Error reading token.json: {str(e)}")
            
            if not creds or not creds.valid:
                if creds and creds.expired and creds.refresh_token:
                    creds.refresh(Request())
                else:
                    try:
                        flow = InstalledAppFlow.from_client_secrets_file(
                            self.gmail_credentials_path, GMAIL_SCOPES)
                        creds = flow.run_local_server(port=0)
                        with open('token.json', 'w') as token:
                            token.write(creds.to_json())
                    except Exception as e:
                        self.update_log(f"Error in Gmail OAuth flow: {str(e)}")
                        self.gui_queue.put(lambda: messagebox.showerror("Error", 
                            f"Gmail authentication failed: {str(e)}"))
                        return
            
            service = build('gmail', 'v1', credentials=creds)
            email_count = 0
            start_time = time.time()
            
            for index, recipient in enumerate(recipients):
                if self.stop_event.is_set():
                    self.update_log("Email sending stopped.")
                    break
                
                if email_count >= GMAIL_LIMIT_EMAILS or (time.time() - start_time) >= GMAIL_LIMIT_TIME:
                    self.update_log("Approaching Gmail API rate limit, pausing for 90 seconds.")
                    time.sleep(GMAIL_LIMIT_TIME)
                    email_count = 0
                    start_time = time.time()
                
                self.process_emails([recipient], from_email, service=service)
                email_count += 1
                time.sleep(0.5)
        
        except Exception as e:
            self.update_log(f"Error in Gmail API: {str(e)}")
            self.gui_queue.put(lambda: messagebox.showerror("Error", f"Gmail API error: {str(e)}"))

    def send_icloud_smtp_emails(self, recipients):
        """Send using iCloud SMTP."""
        from_email = self.sender_email_entry.get()
        password = self.sender_password_entry.get()
        
        if not from_email or not password:
            self.update_log("Error: Sender email and app-specific password required for iCloud SMTP.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", 
                "Sender email and app-specific password required for iCloud SMTP."))
            return
        
        batch_size = int(self.emails_per_batch.get().strip() or len(recipients))
        recipients = recipients[:batch_size]
        
        try:
            server = smtplib.SMTP("smtp.mail.me.com", 587)
            server.starttls()
            server.login(from_email, password)
            
            try:
                self.process_emails(recipients, from_email, server=server)
            finally:
                server.quit()
        
        except smtplib.SMTPException as e:
            self.update_log(f"iCloud SMTP error: {str(e)}")
            self.gui_queue.put(lambda: messagebox.showerror("Error", f"iCloud SMTP error: {str(e)}"))

    def send_gmail_smtp_emails(self, recipients):
        """Send using Gmail SMTP."""
        from_email = self.sender_email_entry.get()
        password = self.sender_password_entry.get()
        
        if not from_email or not password:
            self.update_log("Error: Sender email and app-specific password required for Gmail SMTP.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", 
                "Sender email and app-specific password required for Gmail SMTP."))
            return
        
        batch_size = int(self.emails_per_batch.get().strip() or len(recipients))
        recipients = recipients[:batch_size]
        
        try:
            server = smtplib.SMTP("smtp.gmail.com", 587)
            server.starttls()
            server.login(from_email, password)
            email_count = 0
            start_time = time.time()
            
            try:
                for i in range(0, len(recipients), 10):
                    if self.stop_event.is_set():
                        self.update_log("Email sending stopped.")
                        break
                    
                    batch = recipients[i:i + 10]
                    
                    if email_count >= GMAIL_LIMIT_EMAILS or (time.time() - start_time) >= GMAIL_LIMIT_TIME:
                        self.update_log("Approaching Gmail SMTP rate limit, pausing for 90 seconds.")
                        time.sleep(GMAIL_LIMIT_TIME)
                        email_count = 0
                        start_time = time.time()
                    
                    self.process_emails(batch, from_email, server=server)
                    email_count += len(batch)
                    time.sleep(0.5)
            finally:
                server.quit()
        
        except smtplib.SMTPException as e:
            self.update_log(f"Gmail SMTP error: {str(e)}")
            self.gui_queue.put(lambda: messagebox.showerror("Error", f"Gmail SMTP error: {str(e)}"))
            self.stop_event.set()

    def process_emails(self, recipients, from_email, server=None, service=None):
        """Process a batch of emails."""
        body_template = self.body_textbox.get("1.0", tk.END).strip()
        
        if not body_template and not self.html_var.get():
            self.update_log("Error: Email body empty.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", "Email body cannot be empty."))
            return
        
        # Validate timer_interval
        try:
            timer_interval = float(self.timer_entry.get().strip() or str(self.config['default_timer']))
            if timer_interval < 0:
                raise ValueError("Negative value")
        except ValueError:
            self.update_log(f"Error: Invalid timer interval. Using default {self.config['default_timer']} seconds.")
            timer_interval = float(self.config['default_timer'])
        
        # Validate batch_size
        try:
            batch_size = int(self.emails_per_batch.get().strip() or "10")
            if batch_size <= 0:
                raise ValueError("Batch size must be positive")
        except ValueError:
            self.update_log("Error: Invalid batch size. Using default 10.")
            batch_size = 10
        
        # Validate auto_pause_count
        auto_pause_count = None
        try:
            if self.auto_pause_count.get().strip() and self.auto_pause_var.get():
                auto_pause_count = int(self.auto_pause_count.get())
                if auto_pause_count <= 0:
                    raise ValueError("Auto pause count must be positive")
        except ValueError as e:
            self.update_log(f"Warning: Invalid auto pause count ({str(e)}). Auto pause disabled.")
        
        # Random pause options
        random_pause_options = [3, 4, 5, 6]
        
        for i in range(0, len(recipients), batch_size):
            if self.stop_event.is_set():
                self.update_log("Email sending stopped.")
                self.gui_queue.put(lambda: self.status_label.configure(text="Status: Stopped"))
                break
            
            if self.pause_event.is_set():
                self.update_log("Paused, waiting to resume...")
                self.gui_queue.put(lambda: self.status_label.configure(
                    text=f"Status: Manual Pause ({from_email})"))
                while self.pause_event.is_set() and not self.stop_event.is_set():
                    time.sleep(0.5)
                self.gui_queue.put(lambda: self.status_label.configure(text="Status: Sending"))
            
            batch = recipients[i:i + batch_size]
            for recipient in batch:
                if self.stop_event.is_set():
                    self.update_log("Email sending stopped mid-batch.")
                    self.gui_queue.put(lambda: self.status_label.configure(text="Status: Stopped"))
                    break
                
                if isinstance(recipient, dict):
                    email = recipient.get("Email", recipient.get("email", ""))
                    name = recipient.get("Name", recipient.get("name", ""))
                    last_name = recipient.get("Last Name", recipient.get("last_name", ""))
                else:
                    email = recipient
                    name = ""
                    last_name = ""
                
                customer_id = self.generate_customer_id()
                membership_id = self.generate_membership_id()
                subject = self.get_subject(name, last_name, recipient if isinstance(recipient, dict) else None, 
                                          customer_id, membership_id)
                
                retries = 3
                for attempt in range(retries):
                    try:
                        msg = self.compose_email(email, from_email, subject, name, last_name, 
                                                customer_id, membership_id)
                        
                        if server:
                            server.send_message(msg)
                        elif service:
                            raw_message = base64.urlsafe_b64encode(msg.as_bytes()).decode()
                            service.users().messages().send(userId='me', body={'raw': raw_message}).execute()
                        
                        with self.sent_emails_lock:
                            self.sent_emails.add(email)
                            self.emails_sent += 1
                        
                        self.update_log(f"Email sent to {email}")
                        self.gui_queue.put(lambda e=email: self.status_label.configure(text=f"Status: Sent to {e}"))
                        self.update_progress(self.emails_sent, self.total_emails)
                        
                        if from_email not in self.sender_logs:
                            self.sender_logs[from_email] = []
                        
                        timestamp = datetime.now().isoformat()
                        with self.sender_logs_lock:
                            self.sender_logs[from_email].append((email, True, "", timestamp))
                        self.gui_queue.put(self.update_log_display)
                        
                        break
                    
                    except Exception as e:
                        self.update_log(f"Attempt {attempt + 1} failed for {email}: {str(e)}")
                        self.gui_queue.put(lambda e=email: self.status_label.configure(
                            text=f"Status: Failed for {e}"))
                        
                        if "auth" in str(e).lower() or "login" in str(e).lower() or "credential" in str(e).lower():
                            self.update_log(f"Sender failure detected: {str(e)}. Stopping all sending.")
                            self.stop_event.set()
                            return
                        
                        if attempt == retries - 1:
                            self.update_log(f"Error sending to {email} after {retries} attempts: {str(e)}")
                            
                            if from_email not in self.sender_logs:
                                self.sender_logs[from_email] = []
                            
                            timestamp = datetime.now().isoformat()
                            with self.sender_logs_lock:
                                self.sender_logs[from_email].append((email, False, str(e), timestamp))
                            self.gui_queue.put(self.update_log_display)
                        
                        time.sleep(1)
                
                # Auto pause
                if auto_pause_count and self.emails_sent % auto_pause_count == 0:
                    self.update_log(f"Auto pause after {self.emails_sent} emails for {auto_pause_count} seconds from {from_email}")
                    self.gui_queue.put(lambda: self.status_label.configure(
                        text=f"Status: Auto Pause ({from_email})"))
                    time.sleep(auto_pause_count)
                    self.update_log("Auto pause completed, resuming.")
                    self.gui_queue.put(lambda: self.status_label.configure(text="Status: Sending"))
                
                # Regular pause
                if not self.stop_event.is_set() and not self.pause_event.is_set():
                    pause = random.choice(random_pause_options) if self.random_pause_var.get() else timer_interval
                    self.update_log(f"{'Random' if self.random_pause_var.get() else 'Fixed'} pause of {pause} seconds for {from_email}")
                    time.sleep(pause)
        
        if server:
            try:
                server.quit()
            except:
                pass
        
        if self.emails_sent >= self.total_emails and not self.stop_event.is_set():
            self.gui_queue.put(self.show_completion_popup)
        
        self.gui_queue.put(lambda: self.send_button.configure(state="normal"))

    def update_progress(self, sent, total):
        """Update progress bar with animation."""
        def update():
            if total > 0:
                current = self.progress_bar.get()
                target = sent / total
                step = (target - current) / 10
                
                for i in range(10):
                    self.progress_bar.set(current + step * i)
                    self.app.update_idletasks()
                    time.sleep(0.05)
                
                self.progress_bar.set(target)
                percentage = (sent / total) * 100
                pending = total - sent
                self.progress_label.configure(
                    text=f"({sent}/{total} sent, {pending} pending, {percentage:.1f}% complete)")
            else:
                self.progress_bar.set(0)
                self.progress_label.configure(text="Progress: 0 / 0")
        
        try:
            self.gui_queue.put(update, timeout=1)
        except queue.Full:
            self.update_log(f"GUI queue full, dropping progress update: {sent}/{total}")

    # ==================== EMAIL COMPOSITION ====================
    
    def compose_email(self, to_email, from_email, subject, name, last_name, customer_id, membership_id):
        """Compose email message."""
        sender_name = self.sender_name_entry.get().strip() or "Sender"
        est = pytz.timezone('US/Eastern')
        current_time = datetime.now(est).strftime('%B %d, %Y, %I:%M %p').replace(' 0', '')
        
        msg = MIMEMultipart()
        msg['From'] = f"{sender_name} <{from_email}>"
        msg['To'] = to_email
        msg['Subject'] = subject
        
        # Add unsubscribe headers
        if self.include_unsubscribe_var.get():
            link = self.unsubscribe_link.strip()
            if not link:
                link = "https://example.com/unsubscribe"
                self.update_log("Warning: Empty unsubscribe link; using default.")
            
            if not link.startswith(('http://', 'https://')):
                link = 'https://' + link
            
            from_domain = from_email.split('@')[1] if '@' in from_email else "example.com"
            msg['List-Unsubscribe'] = f"<{link}>, <mailto:unsubscribe@{from_domain}?subject=unsubscribe>"
            msg['List-Unsubscribe-Post'] = 'List-Unsubscribe=One-Click'
            self.update_log(f"Unsubscribe link attached: {link} with mailto:unsubscribe@{from_domain}")
        
        transaction_id = self.generate_transaction_id()
        amount = self.generate_amount()
        customer_id = customer_id or self.generate_customer_id()
        membership_id = membership_id or self.generate_membership_id()
        
        body_template = self.body_textbox.get("1.0", tk.END).strip()
        html_content = self.html_textbox.get("1.0", tk.END).strip() if self.html_var.get() else ""
        
        def replace_placeholders(text):
            return (text
                    .replace("[[current_time]]", current_time)
                    .replace("[[to_email]]", to_email)
                    .replace("[[name]]", name)
                    .replace("[[last_name]]", last_name)
                    .replace("[[transaction_id]]", transaction_id)
                    .replace("[[membership_id]]", membership_id)
                    .replace("[[customer_id]]", customer_id)
                    .replace("[[amount]]", amount))
        
        body_template = replace_placeholders(body_template)
        html_content = replace_placeholders(html_content) if html_content else ""
        
        # Inject unsubscribe link into body
        body_template = self.prepare_email_body(body_template, to_email, False)
        html_content = self.prepare_email_body(html_content, to_email, True) if html_content else ""
        
        is_html = self.html_var.get() and html_content
        format_type = self.format_var.get()
        random_name = self.generate_random_filename()
        
        if body_template:
            msg.attach(MIMEText(body_template, 'plain'))
        
        if is_html and format_type == "HTML":
            msg.attach(MIMEText(html_content, 'html'))
        
        elif is_html and format_type == "JPG":
            output_path = self.convert_html_to_image(html_content, format_type)
            if output_path and os.path.exists(output_path):
                with open(output_path, "rb") as f:
                    img = MIMEImage(f.read())
                    img.add_header('Content-ID', f'<img_{len(self.attachments)+1}>')
                    img.add_header('Content-Disposition', 'inline', 
                                  filename=f"{random_name}.{format_type.lower()}")
                    msg.attach(img)
                os.unlink(output_path)
                self.update_log(f"Attached HTML as {format_type}: {output_path}")
            else:
                self.update_log(f"Failed to convert HTML to {format_type}")
        
        elif is_html and format_type == "PDF":
            if WEASYPRINT_AVAILABLE:
                output_path = self.convert_html_to_pdf(html_content)
                if output_path and os.path.exists(output_path):
                    with open(output_path, "rb") as f:
                        attachment = MIMEApplication(f.read(), Name=f"{random_name}.pdf")
                        attachment['Content-Disposition'] = f'attachment; filename="{random_name}.pdf"'
                        msg.attach(attachment)
                    os.unlink(output_path)
                    self.update_log(f"Attached HTML as PDF: {output_path}")
                else:
                    self.update_log("Failed to convert HTML to PDF")
            else:
                self.update_log("PDF conversion skipped: WeasyPrint not available.")
        
        # Attach files
        for i, file_path in enumerate(self.attachments):
            try:
                file_size_mb = os.path.getsize(file_path) / (1024*1024)
                if file_size_mb > self.config['attachment_max_size_mb']:
                    self.update_log(f"Skipping oversized attachment: {file_path} ({file_size_mb:.1f}MB)")
                    continue
                
                with open(file_path, "rb") as f:
                    if file_path.lower().endswith(('.png', '.jpg', '.jpeg', '.gif')):
                        img = MIMEImage(f.read())
                        img.add_header('Content-ID', f'<img_{i+1}>')
                        img.add_header('Content-Disposition', 'inline', 
                                      filename=os.path.basename(file_path))
                        msg.attach(img)
                    else:
                        attachment = MIMEApplication(f.read(), Name=os.path.basename(file_path))
                        attachment['Content-Disposition'] = f'attachment; filename="{os.path.basename(file_path)}"'
                        msg.attach(attachment)
            except Exception as e:
                self.update_log(f"Error attaching file {file_path}: {str(e)}")
        
        return msg

    def prepare_email_body(self, body, recipient, html_mode):
        """Append unsubscribe link to body."""
        if not self.include_unsubscribe_var.get():
            return body
        
        encoded_recipient = base64.urlsafe_b64encode(recipient.encode('utf-8')).decode('utf-8').rstrip('=')
        unsubscribe_url = f"{self.unsubscribe_link}?token={encoded_recipient}"
        
        if html_mode:
            unsubscribe_html = f"""
            <div style="font-size:12px; color:#888; margin-top:20px; padding-top:10px; border-top:1px solid #eee; text-align:center;">
                <p>If you no longer wish to receive these emails, please <a href="{unsubscribe_url}" style="color:#007bff;">unsubscribe here</a>.</p>
            </div>
            """
            return body + unsubscribe_html
        else:
            return body + f"\n\n---\nIf you no longer wish to receive these emails, unsubscribe here: {unsubscribe_url}\n---"

    # ==================== CONTINUED IN NEXT MESSAGE ====================
    # 
        # ==================== HTML/PDF CONVERSION ====================
    
    def convert_html_to_image(self, html_content, output_format):
        """Convert HTML to image using wkhtmltoimage."""
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False, encoding='utf-8') as temp_html:
                temp_html.write(html_content)
                temp_html_path = temp_html.name
            
            random_name = self.generate_random_filename()
            output_path = tempfile.mktemp(suffix=f'_{random_name}.{output_format.lower()}')
            
            cmd = [
                WKHTMLTOIMAGE_PATH, 
                '--format', output_format.lower(), 
                '--quiet', 
                '--width', '600', 
                '--enable-local-file-access', 
                temp_html_path, 
                output_path
            ]
            
            creationflags = 0
            if platform.system() == "Windows":
                creationflags = subprocess.CREATE_NO_WINDOW
            
            subprocess.check_call(cmd, creationflags=creationflags)
            os.unlink(temp_html_path)
            return output_path
        
        except Exception as e:
            self.update_log(f"Error converting HTML to {output_format}: {str(e)}")
            return None

    def convert_html_to_pdf(self, html_content, flat=False):
        """Convert HTML to PDF using WeasyPrint."""
        if not WEASYPRINT_AVAILABLE:
            self.update_log("Error: WeasyPrint is not installed. Cannot convert HTML to PDF.")
            return None
        
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False, encoding='utf-8') as temp_html:
                temp_html.write(html_content)
                temp_html_path = temp_html.name
            
            random_name = self.generate_random_filename()
            output_path = tempfile.mktemp(suffix=f'_{random_name}.pdf')
            
            stylesheets = [] if flat else [CSS(string='@page { size: A4; margin: 0cm; }')]
            HTML(temp_html_path).write_pdf(output_path, stylesheets=stylesheets)
            
            os.unlink(temp_html_path)
            return output_path
        
        except Exception as e:
            self.update_log(f"Error converting HTML to PDF: {str(e)}")
            return None

    # ==================== FILE ATTACHMENT METHODS ====================
    
    def attach_file(self):
        """Attach files to email."""
        file_paths = filedialog.askopenfilenames()
        if file_paths:
            image_extensions = ('.png', '.jpg', '.jpeg', '.gif', '.heic')
            total_size = 0
            max_size_mb = self.config['attachment_max_size_mb']
            
            for file_path in file_paths:
                file_size_mb = os.path.getsize(file_path) / (1024*1024)
                
                if file_size_mb > max_size_mb:
                    messagebox.showwarning("Warning", 
                        f"File {os.path.basename(file_path)} exceeds {max_size_mb}MB limit. Skipping.")
                    continue
                
                total_size += os.path.getsize(file_path)
                if total_size / (1024*1024) > max_size_mb:
                    messagebox.showwarning("Warning", f"Total attachments exceed {max_size_mb}MB limit.")
                    break
                
                if os.path.isfile(file_path):
                    self.attachments.append(file_path)
                    
                    if file_path.lower().endswith(image_extensions) and self.html_var.get():
                        cid = f"img_{len(self.attachments)}"
                        self.body_textbox.insert(tk.END, 
                            f'<img src="cid:{cid}" alt="{os.path.basename(file_path)}">\n')
                    else:
                        self.body_textbox.insert(tk.END, 
                            f'Attachment: {os.path.basename(file_path)}\n')
                    
                    # Display preview
                    try:
                        img = Image.open(file_path)
                        img = img.resize((100, 100), Image.LANCZOS)
                        self.image_photo = ImageTk.PhotoImage(img)
                        self.image_label.configure(image=self.image_photo, text="")
                    except Exception as e:
                        self.update_log(f"Error displaying image {file_path}: {str(e)}")
                        self.image_label.configure(image="", text="Error loading image")
                else:
                    self.update_log(f"Ignored invalid file: {file_path}")
                    messagebox.showwarning("Warning", f"Invalid file: {file_path}")
            
            self.file_label.configure(text=", ".join([os.path.basename(f) for f in self.attachments]))
            self.remove_file_button.place(x=290, y=410)

    def remove_file(self):
        """Remove all attached files."""
        self.attachments = []
        self.file_label.configure(text="")
        self.remove_file_button.place_forget()
        self.configure["attachment"] = None
        self.image_label.configure(image="")
        self.image_photo = None
        self.update_log("Files removed.")

    def add_html_file(self):
        """Add HTML file to HTML textbox."""
        if not self.html_var.get():
            self.update_log("Error: HTML Body must be enabled to add HTML content.")
            self.gui_queue.put(lambda: messagebox.showwarning("Warning", 
                "Please enable HTML Body to add HTML content."))
            return
        
        file_path = filedialog.askopenfilename(filetypes=[("HTML files", "*.html")])
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as file:
                    html_content = file.read()
                    self.html_textbox.configure(state='normal')
                    self.html_textbox.delete("1.0", tk.END)
                    self.html_textbox.insert("1.0", html_content)
                    self.html_textbox.configure(state='normal')
                    self.update_log(f"HTML file loaded: {os.path.basename(file_path)}")
                    self.gui_queue.put(lambda: messagebox.showinfo("Success", 
                        f"HTML file loaded: {os.path.basename(file_path)}"))
            except Exception as e:
                self.update_log(f"Error loading HTML file: {str(e)}")
                self.gui_queue.put(lambda: messagebox.showerror("Error", 
                    f"Failed to load HTML file: {str(e)}"))
                self.html_textbox.configure(state='normal')

    # ==================== PREVIEW METHODS ====================
    
    def preview_html(self):
        """Preview HTML/body content in browser."""
        body_template = self.body_textbox.get("1.0", tk.END).strip()
        html_content = self.html_textbox.get("1.0", tk.END).strip()
        format_type = self.format_var.get()
        random_name = self.generate_random_filename()

        if not (body_template or html_content):
            self.update_log("Error: No content to preview.")
            self.gui_queue.put(lambda: messagebox.showerror("Error", 
                "Please enter content in the body or HTML field"))
            return

        est = pytz.timezone('US/Eastern')
        current_time = datetime.now(est).strftime('%B %d, %Y %I:%M %p').replace(' 0', '')
        name, last_name = "John", "Doe"
        to_email = "recipient@example.com"
        transaction_id = self.generate_transaction_id()
        membership_id = self.generate_membership_id()
        customer_id = self.generate_customer_id()
        amount = self.generate_amount()

        def replace_placeholders(text):
            return (text
                    .replace("[[current_time]]", current_time)
                    .replace("[[to_email]]", to_email)
                    .replace("[[name]]", name)
                    .replace("[[last_name]]", last_name)
                    .replace("[[transaction_id]]", transaction_id)
                    .replace("[[membership_id]]", membership_id)
                    .replace("[[customer_id]]", customer_id)
                    .replace("[[amount]]", amount))

        body_template = replace_placeholders(body_template)
        html_content = replace_placeholders(html_content) if html_content else ""

        try:
            if format_type == "HTML":
                content = html_content or html.escape(body_template, quote=True).replace('\n', '<br>')
                with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False, encoding='utf-8') as temp_file:
                    temp_file.write(content)
                    temp_file_path = temp_file.name
                webbrowser.open_new_tab(f'file://{temp_file_path}')
                self.update_log(f"HTML preview opened in new tab: {temp_file_path}")
                self.app.after(5000, lambda: os.unlink(temp_file_path) if os.path.exists(temp_file_path) else None)

            elif format_type == "JPG":
                output_path = self.convert_html_to_image(
                    html_content or html.escape(body_template, quote=True).replace('\n', '<br>'), 
                    format_type
                )
                if output_path and os.path.exists(output_path):
                    with open(output_path, 'rb') as f:
                        img_data = base64.b64encode(f.read()).decode()
                    
                    mime_type = 'image/jpeg'
                    escaped_body = html.escape(body_template, quote=True).replace('\n', '<br>')
                    content = f"""
                    <html>
                    <head>
                        <title>Email Preview - {format_type}</title>
                    </head>
                    <body>
                        <h2>Email Preview ({format_type})</h2>
                        <img src="data:{mime_type};base64,{img_data}" alt="Email Preview">
                        <p>Body content (if any):</p>
                        <p>{escaped_body}</p>
                    </body>
                    </html>
                    """
                    
                    with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False, encoding='utf-8') as temp_file:
                        temp_file.write(content)
                        temp_file_path = temp_file.name
                    
                    webbrowser.open_new_tab(f'file://{temp_file_path}')
                    self.update_log(f"{format_type} preview opened in new tab: {temp_file_path}")
                    os.unlink(output_path)
                    self.app.after(5000, lambda: os.unlink(temp_file_path) if os.path.exists(temp_file_path) else None)
                else:
                    self.update_log(f"Error: Failed to convert HTML to {format_type} for preview.")
                    self.gui_queue.put(lambda: messagebox.showerror("Error", 
                        f"Failed to convert HTML to {format_type} for preview."))

            elif format_type == "PDF":
                if not WEASYPRINT_AVAILABLE:
                    self.update_log("Error: WeasyPrint is not installed. Cannot preview as PDF.")
                    self.gui_queue.put(lambda: messagebox.showerror("Error", 
                        "WeasyPrint is not installed. Cannot preview as PDF."))
                    return
                
                output_path = self.convert_html_to_pdf(
                    html_content or html.escape(body_template, quote=True).replace('\n', '<br>')
                )
                if output_path and os.path.exists(output_path):
                    with open(output_path, 'rb') as f:
                        pdf_data = base64.b64encode(f.read()).decode()
                    
                    escaped_body = html.escape(body_template, quote=True).replace('\n', '<br>')
                    content = f"""
                    <html>
                    <head>
                        <title>Email Preview - PDF</title>
                    </head>
                    <body>
                        <h2>Email Preview (PDF)</h2>
                        <p>PDF preview embedded below (may not render in all browsers):</p>
                        <embed src="data:application/pdf;base64,{pdf_data}" type="application/pdf" width="100%" height="600px">
                        <p>Body content (if any):</p>
                        <p>{escaped_body}</p>
                        <p><a href="data:application/pdf;base64,{pdf_data}" download="{random_name}.pdf">Download PDF</a></p>
                    </body>
                    </html>
                    """
                    
                    with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False, encoding='utf-8') as temp_file:
                        temp_file.write(content)
                        temp_file_path = temp_file.name
                    
                    webbrowser.open_new_tab(f'file://{temp_file_path}')
                    self.update_log(f"PDF preview opened in new tab: {temp_file_path}")
                    os.unlink(output_path)
                    self.app.after(5000, lambda: os.unlink(temp_file_path) if os.path.exists(temp_file_path) else None)
                else:
                    self.update_log("Error: Failed to convert HTML to PDF for preview.")
                    self.gui_queue.put(lambda: messagebox.showerror("Error", 
                        "Failed to convert HTML to PDF for preview."))

        except Exception as e:
            self.update_log(f"Error generating preview: {str(e)}")
            self.gui_queue.put(lambda: messagebox.showerror("Error", 
                f"Error generating preview: {str(e)}"))

    # ==================== TAGS POPUP ====================
    
    def show_tags_popup(self):
        """Show tags selection popup."""
        popup = Toplevel(self.app)
        popup.title("Select Tag")
        popup.geometry("300x400")
        popup.resizable(False, False)
        popup.configure(bg="#2b2b2b")

        tags = [
            "[[current_time]]", "[[to_email]]", "[[name]]", "[[last_name]]",
            "[[transaction_id]]", "[[membership_id]]", "[[customer_id]]", "[[amount]]"
        ]
        
        for i, tag in enumerate(tags):
            ctk.CTkButton(
                popup, text=tag, font=("Arial", 13, "bold"), text_color="#FFFFFF",
                fg_color="#1A8B53", width=250,
                command=lambda t=tag: self.insert_tag(t, popup)
            ).place(x=25, y=30 + i * 40)

        ctk.CTkButton(popup, text="Close", font=("Arial", 13, "bold"), text_color="#FFFFFF",
                      fg_color="#1A8B53", width=80, 
                      command=lambda: self.close_preview_popup(popup)).place(x=110, y=350)
        
        self.image_preview_windows.append(popup)
        popup.protocol("WM_DELETE_WINDOW", lambda: self.close_preview_popup(popup))

    def insert_tag(self, tag, popup):
        """Insert tag into body or HTML textbox."""
        target_textbox = self.html_textbox if self.html_var.get() else self.body_textbox
        target_textbox.configure(state=NORMAL)
        target_textbox.insert(tk.END, tag)
        target_textbox.configure(state=NORMAL if target_textbox == self.body_textbox else DISABLED)
        self.update_log(f"Inserted tag: {tag}")
        self.close_preview_popup(popup)

    def close_preview_popup(self, popup):
        """Safe popup cleanup."""
        if popup in self.image_preview_windows:
            self.image_preview_windows.remove(popup)
        try:
            popup.destroy()
        except tk.TclError:
            pass
        except Exception as e:
            self.update_log(f"Error closing popup: {str(e)}")

    # ==================== LOGGING METHODS ====================
    
    def show_log_window(self):
        """Show detailed log window."""
        if hasattr(self, 'log_window') and self.log_window and self.log_window.winfo_exists():
            self.log_window.lift()
            self.update_log_display()
            return
        
        self.log_window = ctk.CTkToplevel(self.app)
        self.log_window.title("Email Sending Logs - MAIL_STORM v2.5")
        self.log_window.geometry("600x500")
        self.log_window.minsize(500, 400)
        
        # Main container
        main_container = ctk.CTkFrame(self.log_window)
        main_container.pack(fill='both', expand=True, padx=5, pady=5)
        main_container.grid_columnconfigure(0, weight=1)
        main_container.grid_rowconfigure(2, weight=1)
        
        # Control frame
        control_frame = ctk.CTkFrame(main_container)
        control_frame.grid(row=0, column=0, sticky='ew', padx=5, pady=2)
        control_frame.grid_columnconfigure(0, weight=2)
        control_frame.grid_columnconfigure(1, weight=1)
        
        # Search entry
        self.search_entry = ctk.CTkEntry(control_frame, placeholder_text="Search logs...")
        self.search_entry.grid(row=0, column=0, sticky='ew', padx=(5, 2), pady=2)
        self.search_entry.bind("<KeyRelease>", self.search_logs)
        
        # Filter combo
        self.filter_var = tk.StringVar(value="All")
        filter_values = ["All", "Success", "Error", "Warning"] + [
            f"Sender: {s['email']}" for s in self.sender_accounts
        ]
        filter_combo = ctk.CTkComboBox(
            control_frame, 
            values=filter_values, 
            variable=self.filter_var,
            command=self.update_log_display,
            width=120
        )
        filter_combo.grid(row=0, column=1, sticky='ew', padx=2, pady=2)
        
        # Buttons frame
        button_frame = ctk.CTkFrame(main_container)
        button_frame.grid(row=1, column=0, sticky='ew', padx=5, pady=2)
        button_frame.grid_columnconfigure((0,1,2), weight=1)
        
        # Action buttons
        clear_button = ctk.CTkButton(
            button_frame, 
            text="Clear Logs",
            font=("Arial", 12, "bold"),
            text_color="#FFFFFF",
            fg_color="#1A8B53",
            width=80,
            command=self.clear_log
        )
        clear_button.grid(row=0, column=0, sticky='ew', padx=2, pady=2)
        
        export_button = ctk.CTkButton(
            button_frame,
            text="Export Logs",
            font=("Arial", 12, "bold"),
            text_color="#FFFFFF",
            fg_color="#1A8B53",
            width=80,
            command=self.export_logs
        )
        export_button.grid(row=0, column=1, sticky='ew', padx=2, pady=2)
        
        refresh_button = ctk.CTkButton(
            button_frame,
            text="Refresh",
            font=("Arial", 12, "bold"),
            text_color="#FFFFFF",
            fg_color="#1A8B53",
            width=80,
            command=self.update_log_display
        )
        refresh_button.grid(row=0, column=2, sticky='ew', padx=2, pady=2)
        
        # Log textbox
        self.log_textbox = ctk.CTkTextbox(
            main_container,
            font=("Arial", 12),
            wrap='word'
        )
        self.log_textbox.grid(row=2, column=0, sticky='nsew', padx=5, pady=2)
        
        # Configure tags
        self.log_textbox.tag_config("success", foreground="green")
        self.log_textbox.tag_config("error", foreground="red")
        self.log_textbox.tag_config("warning", foreground="yellow")
        self.log_textbox.tag_config("info", foreground="white")
        
        # Summary label
        self.summary_label = ctk.CTkLabel(
            main_container,
            text="Total Senders: 0 | Sent: 0 | Failed: 0 | Success Rate: 0.0%",
            font=("Arial", 12, "bold")
        )
        self.summary_label.grid(row=3, column=0, sticky='ew', padx=5, pady=2)
        
        # Initial update
        self.update_log_display()
        
        self.log_window.protocol("WM_DELETE_WINDOW", self.close_log_window)

    def update_log_display(self, search_term=None):
        """Update log display with timestamps and true history (no dedupe for tester)."""
        if not hasattr(self, 'log_window') or not self.log_window or not self.log_window.winfo_exists():
            return
    
        try:
            self.log_textbox.configure(state='normal')
            self.log_textbox.delete("1.0", tk.END)
    
            filter_type = self.filter_var.get() if hasattr(self, "filter_var") else ""
            search_term = (self.search_entry.get() if search_term is None and hasattr(self, "search_entry") else (search_term or "")).lower()
    
            total_sent = 0
            total_failed = 0
    
            # Loop over senders
            for sender, logs in list(self.sender_logs.items()):
                # Sender filter
                if filter_type.startswith("Sender: ") and filter_type != f"Sender: {sender}":
                    continue
    
                # Stats
                sender_sent = sum(1 for log_entry in logs if len(log_entry) >= 2 and log_entry[1])
                sender_failed = len(logs) - sender_sent
                total_sent += sender_sent
                total_failed += sender_failed
    
                # Header once
                sender_header_shown = False
    
                for log_entry in logs:
                    # Handle both 3- and 4-tuples
                    if len(log_entry) == 4:
                        recip, success, err, ts = log_entry
                    elif len(log_entry) == 3:
                        recip, success, err = log_entry
                        ts = ""
                    else:
                        continue
    
                    # Apply filter
                    if filter_type == "Success" and not success:
                        continue
                    if filter_type == "Error" and success:
                        continue
                    if filter_type == "Warning" and "warning" not in (err or "").lower():
                        continue
    
                    log_line = f"{ts} | Recipient: {recip} - {'✅ Success' if success else f'❌ Error: {err}'}"
                    if search_term and search_term not in log_line.lower():
                        continue
    
                    if not sender_header_shown:
                        self.log_textbox.insert(tk.END, f"\nSender: {sender}\n", "info")
                        sender_header_shown = True
    
                    tag = "success" if success else "error"
                    self.log_textbox.insert(tk.END, f"  {log_line}\n", tag)
    
            # Summary
            total = total_sent + total_failed
            success_rate = (total_sent / total * 100) if total > 0 else 0
            summary = (
                f"Summary: {len(self.sender_logs)} senders | "
                f"Sent: {total_sent} | Failed: {total_failed} | "
                f"Success Rate: {success_rate:.1f}%"
            )
    
            if hasattr(self, "summary_label"):
                self.summary_label.configure(text=summary)
    
            self.log_textbox.configure(state='disabled')
            self.log_textbox.see("1.0")
    
        except Exception as e:
            self.update_log(f"Error updating log display: {str(e)}")
            self.log_textbox.configure(state='disabled')

    def search_logs(self, event=None):
        """Search logs by keyword."""
        search_term = self.search_entry.get().lower()
        self.update_log_display(search_term=search_term)

    def export_logs(self):
        """Export logs to text file."""
        file_path = filedialog.asksaveasfilename(defaultextension=".txt", 
                                                 filetypes=[("Text files", "*.txt")])
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as file:
                    file.write(f"Email Sending Log - {time.strftime('%Y-%m-%d %H:%M:%S')}\n\n")
                    for sender, logs in self.sender_logs.items():
                        file.write(f"Sender: {sender}\n")
                        for recip, success, err in logs:
                            timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                            status = "Successful" if success else f"Error: {err or 'Unknown error'}"
                            file.write(f"  Recipient: {recip} - {status} - {timestamp}\n")
                        file.write("\n")
                
                self.update_log("Logs exported successfully.")
                self.gui_queue.put(lambda: messagebox.showinfo("Success", "Logs exported to file."))
            except Exception as e:
                self.update_log(f"Error exporting logs: {str(e)}")
                self.gui_queue.put(lambda: messagebox.showerror("Error", 
                    f"Failed to export logs: {str(e)}"))

    def close_log_window(self):
        """Close log window."""
        self.log_window.destroy()
        self.log_window = None

    def update_log(self, message):
        """Update activity log."""
        def update():
            try:
                self.log_text.configure(state=NORMAL)
                self.log_text.insert(tk.END, 
                    f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - {message}\n")
                self.log_text.see(tk.END)
                self.log_text.configure(state=DISABLED)
            except Exception as e:
                print(f"Error updating log: {str(e)}")
        
        try:
            if self.gui_queue.qsize() < self.config['gui_queue_size']:
                self.gui_queue.put(update, timeout=1)
            else:
                print(f"Dropping log message due to full queue: {message}")
        except queue.Full:
            print(f"GUI queue full, dropping log message: {message}")

    def clear_log(self):
        """Clear activity log."""
        self.log_text.configure(state=NORMAL)
        self.log_text.delete(1.0, tk.END)
        self.log_text.configure(state=DISABLED)
        self.update_log("Log cleared.")

    # ==================== COMPLETION POPUP ====================
    
    def show_completion_popup(self):
        """Display completion popup."""
        with self.emails_sent_lock:
            success_rate = (self.emails_sent / self.total_emails * 100) if self.total_emails > 0 else 0
        
        if not self.stop_event.is_set() and self.emails_sent == self.total_emails:
            popup = ctk.CTkToplevel(self.app)
            popup.title("Sending Complete")
            popup.geometry("400x150")
            popup.resizable(False, False)
            
            # Center popup
            screen_width = popup.winfo_screenwidth()
            screen_height = popup.winfo_screenheight()
            x = (screen_width - 400) // 2
            y = (screen_height - 150) // 2
            popup.geometry(f"400x150+{x}+{y}")
            
            # Summary
            summary = (
                f"Successfully sent {self.emails_sent} of {self.total_emails} emails\n"
                f"Success Rate: {success_rate:.1f}%"
            )
            
            label = ctk.CTkLabel(
                popup, 
                text=summary,
                font=("Arial", 14, "bold")
            )
            label.pack(pady=20)
            
            # Close button
            close_btn = ctk.CTkButton(
                popup,
                text="Close",
                font=("Arial", 12),
                command=popup.destroy
            )
            close_btn.pack(pady=10)
            
            # View Logs button
            logs_btn = ctk.CTkButton(
                popup,
                text="View Logs",
                font=("Arial", 12),
                command=self.show_log_window
            )
            logs_btn.pack(pady=5)
            
            # Rainbow effect
            colors = ["red", "orange", "yellow", "green", "blue", "indigo", "violet"]
            
            def blink(i=0):
                if not popup.winfo_exists():
                    return
                label.configure(text_color=colors[i % len(colors)])
                popup.after(300, blink, i + 1)
            
            blink()
            
            popup.lift()
            popup.focus_force()
            
            self.status_label.configure(
                text=f"Status: Completed - {self.emails_sent} emails sent successfully"
            )
        else:
            status = "Stopped" if self.stop_event.is_set() else "Incomplete"
            self.status_label.configure(
                text=f"Status: {status} - {self.emails_sent}/{self.total_emails} emails sent"
            )

    def update_unsubscribe_link(self):
        """Update unsubscribe link."""
        new_link = self.unsubscribe_entry.get().strip()
        if new_link:
            self.unsubscribe_link = new_link
        else:
            self.unsubscribe_link = "https://example.com/unsubscribe"
        self.update_log(f"Unsubscribe link updated to: {self.unsubscribe_link}")

    # ==================== SENDER MANAGER UI ====================
    
    def open_sender_manager(self):
        """Open sender manager window with auto-load from CSV."""
        if self.send_mode_var.get() != "Multiple SMTP":
            self.update_log("Sender Manager only available in Multiple SMTP mode.")
            messagebox.showwarning("Warning", 
                "Sender Manager is only available in Multiple SMTP mode.")
            return
        
        try:
            # FIXED: Auto-load from CSV files if they exist
            self.auto_load_senders_from_csv()
            
            # Clear cache and row lists
            self.filtered_cache.clear()
            for row_list in [self.sender_rows, self.replacement_rows, self.failed_rows]:
                for row in row_list[:]:
                    if row.get('frame'):
                        try:
                            row['frame'].destroy()
                        except:
                            pass
                    row_list.remove(row)
            
            self.sender_rows = []
            self.replacement_rows = []
            self.failed_rows = []
            
            self.sender_manager_window = ctk.CTkToplevel(self.app)
            self.sender_manager_window.title("Email Sender Manager - MAIL_STORM v2.5")
            self.sender_manager_window.geometry("1200x750")
            self.sender_manager_window.minsize(900, 650)
            self.sender_manager_window.configure(fg_color="#1e1e1e")
            self.sender_manager_window.resizable(True, True)
            self.sender_manager_window.protocol("WM_DELETE_WINDOW", self.on_sender_manager_close)
            
            # Main container
            main_container = ctk.CTkFrame(self.sender_manager_window, fg_color="transparent")
            main_container.pack(fill="both", expand=True, padx=10, pady=10)
            main_container.grid_rowconfigure(1, weight=1)
            main_container.grid_columnconfigure(0, weight=1)
            
            self.stop_test = False
            self.status_filter_var = tk.StringVar(value="All")
            
            self.sender_manager_window.bind("<Configure>", self.on_sender_manager_resize)
            
            # Toolbar
            toolbar_frame = ctk.CTkFrame(main_container, fg_color="#2b2b2b", height=60)
            toolbar_frame.grid(row=0, column=0, sticky="ew", pady=(0, 5))
            toolbar_frame.grid_columnconfigure(0, weight=1)
            toolbar_frame.pack_propagate(False)
            
            title_label = ctk.CTkLabel(toolbar_frame, text="✉️ Email Sender Manager", 
                                      font=("Arial", 24, "bold"), text_color="#1A8B53")
            title_label.grid(row=0, column=0, sticky="w", padx=15, pady=15)
            
            # Search frame
            search_frame = ctk.CTkFrame(toolbar_frame, fg_color="transparent")
            search_frame.grid(row=0, column=1, sticky="w", padx=20, pady=15)
            ctk.CTkLabel(search_frame, text="🔍", font=("Arial", 16)).pack(side="left", padx=(10, 5))
            self.manager_search_entry = ctk.CTkEntry(search_frame, 
                placeholder_text="Search by email or name...", width=300, height=35)
            self.manager_search_entry.pack(side="left")
            self.manager_search_entry.bind("<KeyRelease>", self.filter_sender_rows)
            
            # Filter frame
            filter_frame = ctk.CTkFrame(toolbar_frame, fg_color="transparent")
            filter_frame.grid(row=0, column=2, sticky="w", padx=10, pady=15)
            ctk.CTkLabel(filter_frame, text="Filter:", font=("Arial", 12, "bold"), 
                        text_color="white").pack(side="left", padx=(0, 5))
            status_filter = ctk.CTkComboBox(filter_frame, 
                values=["All", "Valid", "Partial", "Invalid"], 
                variable=self.status_filter_var, width=120, height=35, 
                command=self.refresh_sections)
            status_filter.pack(side="left")
            
            # Help button
            help_btn = ctk.CTkButton(toolbar_frame, text="❓ Help", width=80, height=35, 
                                    fg_color="#1A8B53", hover_color="#2A9B5A",
                                    command=lambda: messagebox.showinfo("Help", 
                                        "Bulk Add: 1-10 senders | Type auto-fills host/port | Save syncs memory immediately."))
            help_btn.grid(row=0, column=3, sticky="w", padx=10, pady=15)
            
            # Global progress
            self.global_progress = ctk.CTkProgressBar(toolbar_frame, width=200, height=20, mode="determinate")
            self.global_progress.grid(row=0, column=4, sticky="e", padx=20, pady=15)
            self.global_progress.set(0)
            self.global_progress.grid_remove()
            
            # FIXED: Show loaded count
            loaded_count = len(self.sender_accounts) + len(self.replacement_senders) + len(self.failed_senders)
            status_text = f"Loaded {loaded_count} senders from CSV" if loaded_count > 0 else "Ready - Bulk Add up to 10!"
            self.load_status_label = ctk.CTkLabel(toolbar_frame, text=status_text, 
                                                  text_color="yellow" if loaded_count > 0 else "lime")
            self.load_status_label.grid(row=0, column=5, sticky="e", padx=10, pady=15)
            
            # Tabview
            tabview = ctk.CTkTabview(main_container, fg_color="#2b2b2b", 
                                    segmented_button_selected_color="#1A8B53")
            tabview.grid(row=1, column=0, sticky="nsew", pady=5)
            main_tab = tabview.add("Main Senders")
            repl_tab = tabview.add("Replacement Senders")
            failed_tab = tabview.add("Failed Senders")
            
            # Create sections
            def create_sender_section(parent, title, rows_list, is_replacement=False, is_failed=False):
                header_color = "#E74C3C" if is_failed else ("#4A90E2" if is_replacement else "#1A8B53")
                header = ctk.CTkFrame(parent, fg_color=header_color, height=50, corner_radius=10)
                header.pack(fill="x", pady=5, padx=5)
                header.pack_propagate(False)
                header.grid_columnconfigure(0, weight=1)
                
                icon = "⚠️" if is_failed else ("🔄" if is_replacement else "📧")
                ctk.CTkLabel(header, text=f"{icon} {title}", font=("Arial", 18, "bold"), 
                           text_color="white").grid(row=0, column=0, sticky="w", padx=15, pady=15)
                
                # Count label
                self.count_labels = getattr(self, 'count_labels', {})
                count_key = f"{title.lower().replace(' ', '_')}_count"
                self.count_labels[count_key] = ctk.CTkLabel(header, 
                    text=f"Active: {len(rows_list)}", text_color="white", font=("Arial", 12, "bold"))
                self.count_labels[count_key].grid(row=0, column=1, sticky="w", padx=15, pady=15)
                
                # Sort labels
                email_sort_label = ctk.CTkLabel(header, text="📧 Email", 
                    font=("Arial", 12, "bold"), text_color="white", cursor="hand2")
                email_sort_label.grid(row=0, column=2, sticky="w", padx=10, pady=15)
                email_sort_label.bind("<Button-1>", 
                    lambda event: self.sort_rows(rows_list, 'email', parent))
                email_sort_label.bind("<Enter>", 
                    lambda event: email_sort_label.configure(text_color="#FFD700"))
                email_sort_label.bind("<Leave>", 
                    lambda event: email_sort_label.configure(text_color="white"))
                
                status_sort_label = ctk.CTkLabel(header, text="🟢 Status", 
                    font=("Arial", 12, "bold"), text_color="white", cursor="hand2")
                status_sort_label.grid(row=0, column=3, sticky="w", padx=10, pady=15)
                status_sort_label.bind("<Button-1>", 
                    lambda event: self.sort_rows(rows_list, 'status_label', parent))
                status_sort_label.bind("<Enter>", 
                    lambda event: status_sort_label.configure(text_color="#FFD700"))
                status_sort_label.bind("<Leave>", 
                    lambda event: status_sort_label.configure(text_color="white"))
                
                if is_failed:
                    stats_sort_label = ctk.CTkLabel(header, text="📊 Sent / Last", 
                        font=("Arial", 12, "bold"), text_color="white", cursor="hand2")
                    stats_sort_label.grid(row=0, column=4, sticky="w", padx=10, pady=15)
                    stats_sort_label.bind("<Button-1>", 
                        lambda event: self.sort_failed_by_stats(rows_list, parent))
                    stats_sort_label.bind("<Enter>", 
                        lambda event: stats_sort_label.configure(text_color="#FFD700"))
                    stats_sort_label.bind("<Leave>", 
                        lambda event: stats_sort_label.configure(text_color="white"))
                
                if not is_failed:
                    add_btn = ctk.CTkButton(header, text="➕ Add (Bulk)", width=100, height=30, 
                        fg_color="transparent", text_color="white", hover_color=header_color,
                        border_width=1, border_color="white", 
                        command=lambda: self.bulk_add_popup(rows_list, scrollable_frame, is_replacement))
                    add_btn.grid(row=0, column=8, sticky="e", padx=5, pady=10)
                    
                    import_btn = ctk.CTkButton(header, text="📥 Import CSV", width=100, height=30, 
                        fg_color="transparent", text_color="white", hover_color=header_color,
                        border_width=1, border_color="white", 
                        command=lambda: self.bulk_import(is_replacement))
                    import_btn.grid(row=0, column=9, sticky="e", padx=5, pady=10)
                    
                    export_btn = ctk.CTkButton(header, text="📤 Export Tab", width=100, height=30, 
                        fg_color="transparent", hover_color=header_color,
                        border_width=1, border_color="white", 
                        command=lambda: self.export_tab(rows_list))
                    export_btn.grid(row=0, column=10, sticky="e", padx=15, pady=10)
                
                scrollable_frame = ctk.CTkScrollableFrame(parent, fg_color="transparent", 
                                                         scrollbar_button_color="#1f538d")
                scrollable_frame.pack(fill="both", expand=True, padx=5, pady=5)
                
                return scrollable_frame
            
            self.main_inner = create_sender_section(main_tab, "Main Senders", self.sender_rows, False, False)
            self.repl_inner = create_sender_section(repl_tab, "Replacement Senders", 
                                                    self.replacement_rows, True, False)
            self.failed_inner = create_sender_section(failed_tab, "Failed Senders", 
                                                      self.failed_rows, False, True)
            
            self.update_log("Sender Manager opened. Auto-loaded from CSV if available.")
            self.update_log(f"Memory state: Main={len(self.sender_accounts)}, Repl={len(self.replacement_senders)}, Failed={len(self.failed_senders)}")
            
            # Add senders from memory to GUI
            self.add_senders_immediate(self.sender_accounts, self.sender_rows, self.main_inner)
            self.add_senders_immediate(self.replacement_senders, self.replacement_rows, self.repl_inner)
            self.add_senders_immediate(self.failed_senders, self.failed_rows, self.failed_inner)
            
            # Buttons Frame
            buttons_frame = ctk.CTkFrame(main_container, fg_color="#2B2B2B", height=70)
            buttons_frame.grid(row=2, column=0, sticky="ew", pady=(5, 0))
            buttons_frame.grid_columnconfigure(1, weight=1)
            for col in range(2, 6):
                buttons_frame.grid_columnconfigure(col, minsize=100)
            buttons_frame.pack_propagate(False)
            
            self.test_progress = ctk.CTkProgressBar(buttons_frame, width=250, height=25, mode="indeterminate")
            self.test_progress.grid(row=0, column=0, sticky="w", padx=15, pady=17)
            self.test_progress.set(0)
            self.test_progress.grid_remove()
            
            self.status_message = ctk.CTkLabel(buttons_frame, text=status_text, 
                text_color="#00FF00", font=("Arial", 12, "bold"))
            self.status_message.grid(row=0, column=1, sticky="ew", padx=20, pady=20)
            
            refresh_btn = ctk.CTkButton(buttons_frame, text="🔄 Refresh", width=100, height=35, 
                fg_color="#1A8B53", hover_color="#2A9B5A", command=self.refresh_sections)
            refresh_btn.grid(row=0, column=2, sticky="e", padx=5, pady=12)
            
            test_all_btn = ctk.CTkButton(buttons_frame, text="🔍 Test All", width=100, height=35, 
                fg_color="#666666", hover_color="#888888", 
                command=self.test_all_connections_with_progress)
            test_all_btn.grid(row=0, column=3, sticky="e", padx=5, pady=12)
            
            save_btn = ctk.CTkButton(buttons_frame, text="💾 Save", width=80, height=35, 
                fg_color="#1A8B53", hover_color="#2A9B5A", command=self.save_senders)
            save_btn.grid(row=0, column=4, sticky="e", padx=5, pady=12)
            
            cancel_btn = ctk.CTkButton(buttons_frame, text="❌ Cancel", width=80, height=35, 
                fg_color="#E74C3C", hover_color="#C0392B", command=self.confirm_cancel)
            cancel_btn.grid(row=0, column=5, sticky="e", padx=15, pady=12)
            
            # Force refresh
            self.sender_manager_window.after(100, self.refresh_sections)
            self.refresh_test_sender_combo()
            self.update_count_labels()
            
            main_container.update_idletasks()
            self.sender_manager_window.update_idletasks()
        
        except Exception as e:
            self.update_log(f"Failed to open Sender Manager: {str(e)}")
            messagebox.showerror("Error", f"Failed to open Sender Manager: {str(e)}")

    def create_sender_row(self, parent, row_index, sender=None, row_type="main"):
        """Create a single sender row with FIXED auto-fill."""
        entries = {}
        is_failed = row_type == "failed"
        is_repl = row_type == "replacement"
        
        fg_color = "#E74C3C" if is_failed else "#4A90E2" if is_repl else "transparent"
        row_frame = ctk.CTkFrame(parent, fg_color=fg_color, height=35)
        row_frame.grid(row=row_index, column=0, sticky="ew", padx=5, pady=2)
        row_frame.grid_columnconfigure(0, weight=1)
        
        # Email
        email_entry = ctk.CTkEntry(row_frame, width=180, placeholder_text="sender@example.com")
        email_entry.grid(row=0, column=0, padx=5, pady=5, sticky="w")
        entries["email"] = email_entry
        
        # Password
        pass_entry = ctk.CTkEntry(row_frame, width=150, placeholder_text="App password")
        pass_entry.grid(row=0, column=1, padx=5, pady=5)
        entries["password"] = pass_entry
        
        # Type - FIXED: Better initialization
        initial_type = sender.get("type", "smtp") if sender else "smtp"
        type_var = tk.StringVar(value=initial_type)
        type_combo = ctk.CTkComboBox(row_frame, values=list(SMTP_PRESETS.keys()), 
                                    variable=type_var, width=120, state='readonly')
        type_combo.grid(row=0, column=2, padx=5, pady=5)
        entries["type"] = type_combo
        
        # Host
        host_entry = ctk.CTkEntry(row_frame, width=150, placeholder_text="smtp.example.com")
        host_entry.grid(row=0, column=3, padx=5, pady=5)
        entries["host"] = host_entry
        
        # Port
        port_entry = ctk.CTkEntry(row_frame, width=60, placeholder_text="587")
        port_entry.grid(row=0, column=4, padx=5, pady=5)
        entries["port"] = port_entry
        
        # FIXED: Auto-fill host/port BEFORE inserting values
        def initial_auto_fill():
            try:
                selected_type = type_combo.get()
                preset = SMTP_PRESETS.get(selected_type, {})
                
                # Only auto-fill if host is empty (allow manual override)
                if not host_entry.get():
                    host_entry.delete(0, END)
                    host_entry.insert(0, preset.get('host', ''))
                
                if not port_entry.get():
                    port_entry.delete(0, END)
                    port_entry.insert(0, str(preset.get('port', 587)))
                
                print(f"Auto-filled {selected_type}: host={preset.get('host', 'N/A')}, port={preset.get('port', 'N/A')}")
            except Exception as e:
                print(f"Error in initial_auto_fill: {e}")
        
        # Call auto-fill immediately
        self.app.after(50, initial_auto_fill)
        
        # FIXED: Insert sender data AFTER auto-fill
        def insert_sender_data():
            try:
                if sender:
                    # Email
                    if sender.get("email"):
                        email_entry.delete(0, END)
                        email_entry.insert(0, sender["email"])
                    
                    # Password
                    if sender.get("password"):
                        pass_entry.delete(0, END)
                        pass_entry.insert(0, sender["password"])
                    
                    # Type
                    if sender.get("type") and sender["type"] in SMTP_PRESETS:
                        type_combo.set(sender["type"])
                    
                    # Host (override auto-fill if exists in sender)
                    if sender.get("host"):
                        host_entry.delete(0, END)
                        host_entry.insert(0, sender["host"])
                    
                    # Port (override auto-fill if exists in sender)
                    if sender.get("port"):
                        port_entry.delete(0, END)
                        port_entry.insert(0, str(sender["port"]))
            except tk.TclError as e:
                print(f"TclError inserting sender data: {e}")
        
        self.app.after(100, insert_sender_data)
        
        # Credentials
        cred_entry = ctk.CTkEntry(row_frame, width=180, placeholder_text="path/to/credentials.json")
        cred_entry.grid(row=0, column=5, padx=5, pady=5)
        entries["credentials"] = cred_entry
        
        def insert_credentials():
            try:
                if sender and sender.get("credentials"):
                    cred_entry.delete(0, END)
                    cred_entry.insert(0, sender["credentials"])
            except tk.TclError:
                pass
        self.app.after(120, insert_credentials)
        
        # Browse
        browse_btn = ctk.CTkButton(row_frame, text="Browse", width=80, 
            command=lambda: self.browse_credentials(cred_entry))
        browse_btn.grid(row=0, column=6, padx=5, pady=5)
        entries["browse_btn"] = browse_btn
        
        # Status
        status_label = ctk.CTkLabel(row_frame, text="⚪ Not Tested", text_color="gray", width=80)
        status_label.grid(row=0, column=7, padx=5, pady=5)
        entries["status_label"] = status_label
        
        # FIXED: Add Test button
        test_btn = ctk.CTkButton(row_frame, text="Test", fg_color="#666666", width=50,
            command=lambda: self.test_single_sender(entries, status_label))
        test_btn.grid(row=0, column=8, padx=5, pady=5)
        entries["test_btn"] = test_btn
        
        # Progress
        prog_frame = ctk.CTkFrame(row_frame)
        prog_frame.grid(row=0, column=9, padx=5, pady=5, sticky="e")
        progress_bar = ctk.CTkProgressBar(prog_frame, width=100)
        progress_bar.pack(side='left')
        progress_bar.set(0)
        entries["progress_bar"] = progress_bar
        progress_label = ctk.CTkLabel(prog_frame, text="0/0", font=("Arial", 9))
        progress_label.pack(side='left', padx=5)
        entries["progress_label"] = progress_label
        
        # Delete
        del_btn = ctk.CTkButton(row_frame, text="Delete", fg_color="red", width=60, 
            command=lambda: self.delete_sender_row(row_index, row_type))
        del_btn.grid(row=0, column=10, padx=5, pady=5)
        entries["del_btn"] = del_btn
        
        # FIXED: Bind type change to auto-fill
        def on_type_change(event=None):
            self.update_host_port_on_type_change(type_combo, host_entry, port_entry)
        
        type_combo.configure(command=on_type_change)
        
        # Store row
        row_data = {"row_index": row_index, "entries": entries, "sender": sender or {}, "frame": row_frame}
        if row_type == "main":
            self.sender_rows.append(row_data)
        elif row_type == "replacement":
            self.replacement_rows.append(row_data)
        elif row_type == "failed":
            self.failed_rows.append(row_data)
        
        return row_data

    def browse_credentials(self, cred_entry):
        """Browse for credentials file."""
        file_path = filedialog.askopenfilename(filetypes=[("JSON files", "*.json")])
        if file_path:
            cred_entry.delete(0, END)
            cred_entry.insert(0, file_path)

    def test_single_sender(self, entries, status_label):
        """Test a single sender connection and update status."""
        email = entries["email"].get().strip()
        password = entries["password"].get().strip()
        s_type = entries["type"].get()
        host = entries["host"].get().strip()
        port_str = entries["port"].get().strip()
        
        # Validation
        if not email:
            status_label.configure(text="❌ No Email", text_color="red")
            messagebox.showerror("Error", "Email is required!")
            return
        
        if not password and s_type != "gmail_api":
            status_label.configure(text="❌ No Password", text_color="red")
            messagebox.showerror("Error", "Password is required!")
            return
        
        if not host:
            status_label.configure(text="❌ No Host", text_color="red")
            messagebox.showerror("Error", f"SMTP host is required!\n\nTip: Select a type (gmail, att, outlook, etc.) to auto-fill.")
            return
        
        try:
            port = int(port_str) if port_str else 587
        except ValueError:
            status_label.configure(text="❌ Invalid Port", text_color="red")
            messagebox.showerror("Error", "Port must be a number!")
            return
        
        # Update status
        status_label.configure(text="⏳ Testing...", text_color="yellow")
        
        def test_thread():
            try:
                if s_type == "gmail_api":
                    # Gmail API test
                    cred_path = entries["credentials"].get().strip()
                    if not cred_path or not os.path.exists(cred_path):
                        raise Exception("Gmail API credentials file not found")
                    
                    # Just check if file is valid JSON
                    with open(cred_path, 'r') as f:
                        json.load(f)
                    
                    self.gui_queue.put(lambda: status_label.configure(text="✅ Valid", text_color="green"))
                    self.gui_queue.put(lambda: messagebox.showinfo("Success", 
                        f"Gmail API credentials valid for {email}"))
                else:
                    # SMTP test
                    self.update_log(f"Testing SMTP: {email} @ {host}:{port} (SSL: {port == 465})")
                    
                    if port == 465:
                        server = smtplib.SMTP_SSL(host, port, timeout=15)
                        self.update_log(f"Connected via SSL to {host}:{port}")
                    else:
                        server = smtplib.SMTP(host, port, timeout=15)
                        server.starttls()
                        self.update_log(f"Connected via TLS to {host}:{port}")
                    
                    server.login(email, password)
                    server.quit()
                    
                    self.gui_queue.put(lambda: status_label.configure(text="✅ Connected", text_color="green"))
                    self.gui_queue.put(lambda: messagebox.showinfo("Success", 
                        f"✅ Connection successful!\n\n"
                        f"Email: {email}\n"
                        f"Host: {host}\n"
                        f"Port: {port}\n"
                        f"Type: {s_type}"
                    ))
                    self.update_log(f"✅ Test passed for {email}")
            
            except smtplib.SMTPAuthenticationError as e:
                error_msg = f"❌ Authentication failed!\n\nEmail: {email}\n\nPossible issues:\n• Wrong password\n• App-specific password required\n• 2FA not configured\n\nError: {str(e)}"
                self.gui_queue.put(lambda: status_label.configure(text="❌ Auth Failed", text_color="red"))
                self.gui_queue.put(lambda: messagebox.showerror("Authentication Error", error_msg))
                self.update_log(f"❌ Auth failed for {email}: {str(e)}")
            
            except smtplib.SMTPConnectError as e:
                error_msg = f"❌ Connection failed!\n\nHost: {host}\nPort: {port}\n\nPossible issues:\n• Wrong host/port\n• Firewall blocking\n• Service down\n\nError: {str(e)}"
                self.gui_queue.put(lambda: status_label.configure(text="❌ Conn Failed", text_color="red"))
                self.gui_queue.put(lambda: messagebox.showerror("Connection Error", error_msg))
                self.update_log(f"❌ Connection failed for {email}: {str(e)}")
            
            except Exception as e:
                error_msg = f"❌ Test failed!\n\nEmail: {email}\nHost: {host}\nPort: {port}\n\nError: {str(e)}"
                self.gui_queue.put(lambda: status_label.configure(text="❌ Failed", text_color="red"))
                self.gui_queue.put(lambda: messagebox.showerror("Test Failed", error_msg))
                self.update_log(f"❌ Test failed for {email}: {str(e)}")
        
        threading.Thread(target=test_thread, daemon=True).start()

    def add_senders_immediate(self, senders, rows_list, parent):
        """Add senders from memory immediately."""
        for i, sender in enumerate(senders):
            self.create_sender_row(parent, i+1, sender, 
                row_type="main" if rows_list is self.sender_rows else 
                         "replacement" if rows_list is self.replacement_rows else "failed")
        self.regrid_rows(rows_list, parent)

    def regrid_rows(self, rows_list, parent):
        """Regrid all rows in order."""
        for i, row in enumerate(rows_list):
            row["row_index"] = i + 1
            row["frame"].grid(row=i+1, column=0, sticky="ew")

    def add_sender_row_to_section(self, rows_list, parent):
        """Add new empty sender row."""
        row_index = len(rows_list) + 1
        row_type = "main" if rows_list is self.sender_rows else "replacement" if rows_list is self.replacement_rows else "failed"
        
        new_sender = {
            "email": "",
            "password": "",
            "type": "smtp",
            "host": "",
            "port": 587,
            "credentials": None
        }
        
        row_data = self.create_sender_row(parent, row_index, new_sender, row_type=row_type)
        
        target_list = self.sender_accounts if row_type == "main" else self.replacement_senders if row_type == "replacement" else self.failed_senders
        with self.sender_accounts_lock:
            target_list.append(new_sender)
        
        self.regrid_rows(rows_list, parent)
        
        max_limit = MAX_MAIN_SENDERS if row_type == "main" else MAX_REPL_SENDERS
        if len(target_list) > max_limit:
            messagebox.showwarning("Limit", f"Max {max_limit} senders for this tab. Extra ignored.")
        
        self.update_log(f"Added new {row_type} sender (total: {len(target_list)})")
        self.update_count_labels()
        if row_type == "main":
            self.refresh_test_sender_combo()

    def bulk_add_popup(self, rows_list, parent, is_replacement=False):
        """Bulk add popup for 1-10 senders."""
        popup = Toplevel(self.sender_manager_window)
        popup.title(f"Bulk Add {'Replacement' if is_replacement else 'Main'} Senders")
        popup.geometry("300x200")
        popup.resizable(False, False)
        popup.grab_set()

        ctk.CTkLabel(popup, text="Number to add (1-10):", font=("Arial", 12), text_color="#000000").pack(pady=10)
        num_var = tk.StringVar(value="1")
        num_entry = ctk.CTkEntry(popup, textvariable=num_var, width=100)
        num_entry.pack(pady=5)
        
        def add_bulk():
            try:
                num = int(num_var.get())
                if 1 <= num <= 10:
                    max_limit = MAX_REPL_SENDERS if is_replacement else MAX_MAIN_SENDERS
                    actual_num = min(num, max_limit - len(rows_list))
                    if actual_num <= 0:
                        messagebox.showwarning("Limit", f"Tab full (max {max_limit}).")
                        return
                    for i in range(actual_num):
                        self.add_sender_row_to_section(rows_list, parent)
                    self.update_log(f"Bulk added {actual_num} {'replacement' if is_replacement else 'main'} senders.")
                    popup.destroy()
                else:
                    messagebox.showwarning("Invalid", "Enter 1-10.")
            except ValueError:
                messagebox.showwarning("Invalid", "Enter a number.")
        
        ctk.CTkButton(popup, text="Add", command=add_bulk, fg_color="#1A8B53").pack(pady=10)
        ctk.CTkButton(popup, text="Cancel", command=popup.destroy).pack(pady=5)

    def bulk_import(self, is_replacement=False):
        """NEW: Import senders from CSV file."""
        file_path = filedialog.askopenfilename(filetypes=[("CSV files", "*.csv")])
        if not file_path:
            return
        
        try:
            df = pd.read_csv(file_path)
            df = self.normalize_csv_columns(df)
            
            required_cols = ['email', 'password', 'type']
            if not all(col in df.columns for col in required_cols):
                messagebox.showerror("Error", f"CSV must contain: {', '.join(required_cols)}")
                return
            
            imported_count = 0
            max_limit = MAX_REPL_SENDERS if is_replacement else MAX_MAIN_SENDERS
            target_list = self.replacement_senders if is_replacement else self.sender_accounts
            rows_list = self.replacement_rows if is_replacement else self.sender_rows
            parent = self.repl_inner if is_replacement else self.main_inner
            
            for _, row in df.iterrows():
                if len(target_list) >= max_limit:
                    messagebox.showwarning("Limit", 
                        f"Reached max {max_limit} senders. Remaining rows skipped.")
                    break
                
                sender = {
                    "email": str(row.get("email", "")).strip(),
                    "password": str(row.get("password", "")).strip(),
                    "type": str(row.get("type", "smtp")).strip().lower(),
                    "host": str(row.get("host", "")).strip(),
                    "port": int(row["port"]) if ("port" in row and not pd.isna(row["port"])) else 587,
                    "credentials": str(row.get("credentials", "")).strip() or None
                }
                
                if not sender["email"]:
                    continue
                
                # Check for duplicates
                if self.check_duplicate_sender(sender["email"]):
                    self.update_log(f"Skipping duplicate sender: {sender['email']}")
                    continue
                
                # Auto-fill host/port from presets if missing
                if not sender["host"] and sender["type"] in SMTP_PRESETS:
                    preset = SMTP_PRESETS[sender["type"]]
                    sender["host"] = preset.get("host", "")
                    sender["port"] = preset.get("port", 587)
                
                with self.sender_accounts_lock:
                    target_list.append(sender)
                
                # Create GUI row
                self.create_sender_row(parent, len(rows_list) + 1, sender, 
                                      row_type="replacement" if is_replacement else "main")
                imported_count += 1
            
            self.regrid_rows(rows_list, parent)
            self.update_count_labels()
            if not is_replacement:
                self.refresh_test_sender_combo()
            
            self.update_log(f"Imported {imported_count} senders from CSV")
            messagebox.showinfo("Success", f"Imported {imported_count} senders")
        
        except Exception as e:
            self.update_log(f"Error importing CSV: {str(e)}")
            messagebox.showerror("Error", f"Failed to import: {str(e)}")

    def export_tab(self, rows_list):
        """Export tab to CSV."""
        path = filedialog.asksaveasfilename(defaultextension=".csv", 
                                           filetypes=[("CSV files", "*.csv")])
        if path:
            try:
                data = []
                for r in rows_list:
                    sender_data = {
                        "email": r["entries"]["email"].get().strip(),
                        "password": r["entries"]["password"].get().strip(),
                        "type": r["entries"]["type"].get(),
                        "host": r["entries"]["host"].get().strip(),
                        "port": int(r["entries"]["port"].get()) if r["entries"]["port"].get().strip() else 587,
                        "credentials": r["entries"]["credentials"].get().strip() or None
                    }
                    if sender_data["email"]:
                        data.append(sender_data)
                
                pd.DataFrame(data).to_csv(path, index=False)
                self.update_log(f"Exported {len(data)} senders to CSV.")
                messagebox.showinfo("Success", f"Exported {len(data)} senders to {os.path.basename(path)}")
            except Exception as e:
                self.update_log(f"Error exporting tab: {str(e)}")
                messagebox.showerror("Error", f"Failed to export: {str(e)}")

    def test_all_connections_with_progress(self):
        """Test all sender connections."""
        self.test_progress.grid()
        self.test_progress.start()
        self.status_message.configure(text="Testing connections...")
        
        def test():
            success = 0
            total = len(self.sender_accounts) + len(self.replacement_senders)
            
            for sender in self.sender_accounts + self.replacement_senders:
                try:
                    s_type = sender.get("type", "smtp")
                    if s_type == "gmail_api":
                        success += 1
                    else:
                        host = sender.get("host") or SMTP_PRESETS.get(s_type, {}).get('host', '')
                        port = sender.get("port") or SMTP_PRESETS.get(s_type, {}).get('port', 587)
                        
                        if port == 465:
                            server = smtplib.SMTP_SSL(host, port, timeout=10)
                        else:
                            server = smtplib.SMTP(host, port, timeout=10)
                            server.starttls()
                        
                        server.login(sender["email"], sender["password"])
                        server.quit()
                        success += 1
                except:
                    pass
            
            self.test_progress.stop()
            self.test_progress.grid_remove()
            self.status_message.configure(text=f"Test complete: {success}/{total} successful")
        
        threading.Thread(target=test, daemon=True).start()

    def save_senders(self):
        """Save all tabs directly from GUI rows to CSV AND update memory with full validation."""
        try:
            saved_files = []
            total_saved = 0
            
            # Main tab
            main_senders_data = []
            if self.sender_rows:
                for i, row in enumerate(self.sender_rows, 1):
                    # Read from GUI
                    email = row["entries"]["email"].get().strip()
                    password = row["entries"]["password"].get().strip()
                    s_type = row["entries"]["type"].get()
                    host = row["entries"]["host"].get().strip()
                    port_str = row["entries"]["port"].get().strip()
                    credentials = row["entries"]["credentials"].get().strip()
                    
                    # Validate and convert port
                    try:
                        port = int(port_str) if port_str else 587
                    except ValueError:
                        port = 587
                    
                    # Create sender dict
                    sender_data = {
                        "email": email,
                        "password": password,
                        "type": s_type,
                        "host": host,
                        "port": port,
                        "credentials": credentials if credentials else None
                    }
                    
                    # Only save if email exists
                    if email:
                        # DEBUG: Print what we're saving
                        print(f"[SAVE DEBUG] Row {i}:")
                        print(f"  Email: {email}")
                        print(f"  Type: {s_type}")
                        print(f"  Host: '{host}' (len={len(host)})")
                        print(f"  Port: {port}")
                        print(f"  Has Password: {bool(password)}")
                        
                        # Validate host/port exist
                        if not host:
                            self.update_log(f"⚠️ Warning: {email} has no SMTP host! Auto-filling from type '{s_type}'")
                            preset = SMTP_PRESETS.get(s_type, {})
                            sender_data['host'] = preset.get('host', '')
                            sender_data['port'] = preset.get('port', 587)
                            print(f"  Auto-filled: host={sender_data['host']}, port={sender_data['port']}")
                        
                        main_senders_data.append(sender_data)
                
                if main_senders_data:
                    # Save to CSV
                    df = pd.DataFrame(main_senders_data)
                    df.to_csv('senders_main.csv', index=False)
                    saved_files.append('senders_main.csv')
                    total_saved += len(main_senders_data)
                    
                    # CRITICAL: Update memory immediately with DEEP COPY
                    with self.sender_accounts_lock:
                        self.sender_accounts = [dict(s) for s in main_senders_data]  # Deep copy
                    
                    # Verify memory update
                    print(f"\n[MEMORY VERIFICATION]")
                    print(f"Main senders in memory: {len(self.sender_accounts)}")
                    for s in self.sender_accounts:
                        print(f"  - {s['email']}: host='{s.get('host', 'MISSING')}', port={s.get('port', 'MISSING')}")
                    
                    self.update_log(f"✅ Updated {len(main_senders_data)} main senders in memory")
            
            # Replacement tab
            repl_senders_data = []
            if self.replacement_rows:
                for i, row in enumerate(self.replacement_rows, 1):
                    email = row["entries"]["email"].get().strip()
                    password = row["entries"]["password"].get().strip()
                    s_type = row["entries"]["type"].get()
                    host = row["entries"]["host"].get().strip()
                    port_str = row["entries"]["port"].get().strip()
                    credentials = row["entries"]["credentials"].get().strip()
                    
                    try:
                        port = int(port_str) if port_str else 587
                    except ValueError:
                        port = 587
                    
                    sender_data = {
                        "email": email,
                        "password": password,
                        "type": s_type,
                        "host": host,
                        "port": port,
                        "credentials": credentials if credentials else None
                    }
                    
                    if email:
                        # Auto-fill missing host/port
                        if not host:
                            preset = SMTP_PRESETS.get(s_type, {})
                            sender_data['host'] = preset.get('host', '')
                            sender_data['port'] = preset.get('port', 587)
                        
                        repl_senders_data.append(sender_data)
                
                if repl_senders_data:
                    pd.DataFrame(repl_senders_data).to_csv('senders_replacement.csv', index=False)
                    saved_files.append('senders_replacement.csv')
                    total_saved += len(repl_senders_data)
                    
                    with self.sender_accounts_lock:
                        self.replacement_senders = [dict(s) for s in repl_senders_data]
                    
                    self.update_log(f"✅ Updated {len(repl_senders_data)} replacement senders in memory")
            
            # Failed tab
            failed_senders_data = []
            if self.failed_rows:
                for i, row in enumerate(self.failed_rows, 1):
                    email = row["entries"]["email"].get().strip()
                    password = row["entries"]["password"].get().strip()
                    s_type = row["entries"]["type"].get()
                    host = row["entries"]["host"].get().strip()
                    port_str = row["entries"]["port"].get().strip()
                    credentials = row["entries"]["credentials"].get().strip()
                    
                    try:
                        port = int(port_str) if port_str else 587
                    except ValueError:
                        port = 587
                    
                    sender_data = {
                        "email": email,
                        "password": password,
                        "type": s_type,
                        "host": host,
                        "port": port,
                        "credentials": credentials if credentials else None
                    }
                    
                    if email:
                        failed_senders_data.append(sender_data)
                
                if failed_senders_data:
                    pd.DataFrame(failed_senders_data).to_csv('senders_failed.csv', index=False)
                    saved_files.append('senders_failed.csv')
                    total_saved += len(failed_senders_data)
                    
                    with self.sender_accounts_lock:
                        self.failed_senders = [dict(s) for s in failed_senders_data]
                    
                    self.update_log(f"✅ Updated {len(failed_senders_data)} failed senders in memory")
            
            # Update test sender combo
            self.refresh_test_sender_combo()
            
            if total_saved == 0:
                self.update_log("No valid senders (with email) to save. Fill email fields in rows.")
                messagebox.showinfo("Info", "No senders to save. Add rows and fill email fields.")
            else:
                # Show detailed summary
                summary_msg = f"✅ Saved {total_saved} senders successfully!\n\n"
                summary_msg += f"Files: {', '.join(saved_files)}\n\n"
                summary_msg += f"Main Senders: {len(main_senders_data)}\n"
                summary_msg += f"Replacement Senders: {len(repl_senders_data)}\n"
                summary_msg += f"Failed Senders: {len(failed_senders_data)}\n\n"
                
                # Verify all have host/port
                missing_config = []
                for s in main_senders_data + repl_senders_data:
                    if not s.get('host') or not s.get('port'):
                        missing_config.append(s['email'])
                
                if missing_config:
                    summary_msg += f"⚠️ WARNING: Missing host/port for:\n{', '.join(missing_config)}\n\n"
                
                summary_msg += "Ready to send emails!"
                
                self.update_log(f"Saved {total_saved} senders to CSV and updated memory: {', '.join(saved_files)}.")
                messagebox.showinfo("Save Successful", summary_msg)
        
        except Exception as e:
            self.update_log(f"Error saving senders: {str(e)}")
            print(f"Save error details: {str(e)}")
            import traceback
            traceback.print_exc()
            messagebox.showerror("Error", f"Failed to save: {str(e)}")

    def update_host_port_on_type_change(self, type_combo, host_entry, port_entry):
        """Auto-fill host/port based on type selection with validation."""
        try:
            t = type_combo.get()
            preset = SMTP_PRESETS.get(t, {'host': '', 'port': 587})
            
            # Always update to ensure consistency
            host_entry.delete(0, END)
            host_entry.insert(0, preset.get('host', ''))
            
            port_entry.delete(0, END)
            port_entry.insert(0, str(preset.get('port', 587)))
            
            # Log for debugging
            self.update_log(f"Auto-filled '{t}': host={preset.get('host', 'EMPTY!')}, port={preset.get('port', 587)}")
            
            # Visual feedback
            if preset.get('host'):
                host_entry.configure(border_color="green")
                port_entry.configure(border_color="green")
                self.app.after(1000, lambda: host_entry.configure(border_color="gray"))
                self.app.after(1000, lambda: port_entry.configure(border_color="gray"))
        except Exception as e:
            self.update_log(f"Error in auto-fill: {str(e)}")
            print(f"Auto-fill error: {str(e)}")


    def sort_rows(self, rows_list, key, parent):
        """Sort rows by key."""
        rows_list.sort(key=lambda r: r["entries"][key].get().lower())
        self.regrid_rows(rows_list, parent)

    def sort_failed_by_stats(self, rows_list, parent):
        """Sort failed rows by stats."""
        rows_list.sort(key=lambda r: r["entries"]["progress_label"].cget("text"))
        self.regrid_rows(rows_list, parent)

    def filter_sender_rows(self, event=None):
        """Filter rows by search and status."""
        search = self.manager_search_entry.get().lower()
        f_type = self.status_filter_var.get()
        
        for row in self.sender_rows + self.replacement_rows + self.failed_rows:
            email = row["entries"]["email"].get().lower()
            status = row["entries"]["status_label"].cget("text").lower()
            show = (not search or search in email) and (f_type == "All" or f_type.lower() in status)
            row["frame"].grid() if show else row["frame"].grid_remove()

    def refresh_sections(self, event=None):
        """Refresh all sections."""
        self.filter_sender_rows()
        self.update_count_labels()

    def update_count_labels(self):
        """Update count labels in headers."""
        for key, label in self.count_labels.items():
            if "main" in key:
                label.configure(text=f"Active: {len(self.sender_rows)}")
            elif "replacement" in key:
                label.configure(text=f"Active: {len(self.replacement_rows)}")
            elif "failed" in key:
                label.configure(text=f"Active: {len(self.failed_rows)}")

    def refresh_test_sender_combo(self):
        """Refresh test sender dropdown."""
        with self.sender_accounts_lock:
            emails = [s["email"] for s in self.sender_accounts if s.get("email")]
        self.test_sender_combo.configure(values=emails)
        self.update_log(f"Refreshed test sender combo with {len(emails)} options.")

    def update_sender_row_progress(self, sender_email, sent, total):
        """Update sender row progress (thread-safe)."""
        def update():
            if not hasattr(self, 'sender_manager_window') or not self.sender_manager_window:
                return
            
            if not self.sender_manager_window.winfo_exists():
                return
            
            progress = sent / max(1, total)
            for row in self.sender_rows + self.replacement_rows + self.failed_rows:
                if row['entries']['email'].get() == sender_email:
                    row['entries']['progress_bar'].set(progress)
                    row['entries']['progress_label'].configure(text=f"{sent}/{total}")
                    break
        
        try:
            self.gui_queue.put(update, timeout=0.5)
        except queue.Full:
            pass

    def delete_sender_row(self, row_index, row_type):
        """Delete a sender row."""
        if row_type == "main":
            if row_index - 1 < len(self.sender_rows):
                del self.sender_rows[row_index - 1]
                self.regrid_rows(self.sender_rows, self.main_inner)
        elif row_type == "replacement":
            if row_index - 1 < len(self.replacement_rows):
                del self.replacement_rows[row_index - 1]
                self.regrid_rows(self.replacement_rows, self.repl_inner)
        elif row_type == "failed":
            if row_index - 1 < len(self.failed_rows):
                del self.failed_rows[row_index - 1]
                self.regrid_rows(self.failed_rows, self.failed_inner)
        self.update_count_labels()

    def confirm_cancel(self):
        """Confirm cancel sender manager."""
        if messagebox.askyesno("Confirm", "Close Sender Manager without saving?"):
            self.on_sender_manager_close()

    def on_sender_manager_resize(self, event):
        """Handle resize event."""
        pass

    def on_sender_manager_close(self):
        """Clean up on manager close."""
        if hasattr(self, 'refresh_debounce_id') and self.refresh_debounce_id is not None:
            try:
                self.sender_manager_window.after_cancel(self.refresh_debounce_id)
            except:
                pass
        
        try:
            if self.sender_manager_window:
                self.sender_manager_window.update_idletasks()
                self.sender_manager_window.destroy()
        except tk.TclError as e:
            self.update_log(f"TclError on close (ignored): {str(e)}")
        except Exception as e:
            self.update_log(f"Error closing manager: {str(e)}")
        
        self.sender_manager_window = None
        if hasattr(self, '_sync_debounce_id'):
            delattr(self, '_sync_debounce_id')
        self.update_log("Sender Manager closed.")

    # ==================== CONTEXT MENU HANDLERS ====================
    
    def show_context_menu(self, event, menu):
        """Show context menu at cursor."""
        try:
            menu.post(event.x_root, event.y_root)
        except Exception as e:
            self.update_log(f"Error showing context menu: {str(e)}")

    def undo(self, textbox):
        """Undo text change."""
        try:
            textbox.edit_undo()
            self.update_log("Undo performed.")
        except tk.TclError:
            self.update_log("Nothing to undo.")
        return "break"

    def redo(self, textbox):
        """Redo text change."""
        try:
            textbox.edit_redo()
            self.update_log("Redo performed.")
        except tk.TclError:
            self.update_log("Nothing to redo.")
        return "break"

    def select_all(self, widget):
        """Select all text in widget."""
        try:
            if isinstance(widget, (ctk.CTkEntry, tk.Entry)):
                widget.select_range(0, tk.END)
                widget.icursor(tk.END)
                self.update_log("Selected all text in entry field.")
            elif isinstance(widget, ctk.CTkTextbox):
                widget.configure(state='normal')
                widget.tag_add("sel", "1.0", tk.END)
                widget.configure(state='disabled' if widget != self.body_textbox else 'normal')
                self.update_log("Selected all text in textbox.")
            return "break"
        except Exception as e:
            self.update_log(f"Error in select_all: {str(e)}")
            return "break"

    def copy_text(self, widget):
        """Copy text from widget."""
        try:
            widget.clipboard_clear()
            if isinstance(widget, ctk.CTkEntry):
                text = widget.get()
                if text:
                    widget.clipboard_append(text)
                    self.update_log("Text copied from entry.")
            elif isinstance(widget, ctk.CTkTextbox):
                text = widget.get("sel.first", "sel.last") if widget.tag_ranges("sel") else widget.get("1.0", tk.END).strip()
                if text:
                    widget.clipboard_append(text)
                    self.update_log("Text copied from textbox.")
        except tk.TclError:
            self.update_log("No text selected to copy.")

    def paste_text(self, widget):
        """Paste text into widget."""
        try:
            text = widget.clipboard_get()
            if isinstance(widget, ctk.CTkEntry):
                widget.delete(0, tk.END)
                widget.insert(0, text)
                self.update_log("Text pasted into entry.")
            elif isinstance(widget, ctk.CTkTextbox):
                widget.configure(state=NORMAL)
                if widget.tag_ranges("sel"):
                    widget.delete("sel.first", "sel.last")
                widget.insert(tk.INSERT, text)
                widget.configure(state=DISABLED if widget != self.body_textbox else NORMAL)
                self.update_log("Text pasted into textbox.")
        except tk.TclError:
            self.update_log("No text to paste.")

    def delete_text(self, widget):
        """Delete text from widget."""
        try:
            if isinstance(widget, ctk.CTkEntry):
                widget.delete(0, tk.END)
                self.update_log("Text deleted from entry.")
            elif isinstance(widget, ctk.CTkTextbox):
                widget.configure(state='normal')
                if widget.tag_ranges("sel"):
                    widget.delete("sel.first", "sel.last")
                else:
                    widget.delete("1.0", tk.END)
                if widget not in [self.body_textbox, self.html_textbox]:
                    widget.configure(state='disabled')
                self.update_log("Text deleted from textbox.")
        except tk.TclError:
            self.update_log("No text selected to delete.")
        except Exception as e:
            self.update_log(f"Error in delete_text: {str(e)}")

    def handle_delete_key(self, event):
        """Handle delete key press."""
        focused = self.app.focus_get()
        if focused in [self.tester_recipient_textbox, self.recipient_textbox] and self.selected_emails:
            self.delete_selected_emails()
            return "break"
        elif focused in [self.subject_entry, self.sender_email_entry, self.sender_password_entry, 
                        self.sender_name_entry, self.to_entry, self.body_textbox, self.html_textbox]:
            return None  # Allow normal delete
        return "break"

    # ==================== UI HELPERS ====================
    
    def toggle_password_visibility(self):
        """Toggle password visibility."""
        current_show = self.sender_password_entry.cget("show")
        if current_show == "*":
            self.sender_password_entry.configure(show="")
            try:
                self.password_toggle_button.configure(image=self.eye_open_img)
            except AttributeError:
                self.password_toggle_button.configure(text="👁️")
        else:
            self.sender_password_entry.configure(show="*")
            try:
                self.password_toggle_button.configure(image=self.eye_closed_img)
            except AttributeError:
                self.password_toggle_button.configure(text="👁️‍🗨️")

    def validate_numeric_entry(self, event):
        """Validate numeric entry fields."""
        entry = event.widget
        value = entry.get()
        
        # Allow empty, digits, and negative sign
        if value == "" or value == "-":
            return
        
        try:
            float(value)
        except ValueError:
            # Remove last character if invalid
            entry.delete(len(value)-1, END)

    def check_gui_queue(self):
        """Process GUI queue updates."""
        try:
            updates = []
            while len(updates) < 20:
                task = self.gui_queue.get_nowait()
                updates.append(task)
        except queue.Empty:
            pass
        except queue.Full:
            error_msg = "Warning: GUI queue full, some updates dropped."
            self.update_log(error_msg)
            print(error_msg)
            updates = []
        
        for task in updates:
            try:
                task()
            except Exception as e:
                error_msg = f"Error executing GUI task: {str(e)}"
                self.update_log(error_msg)
                print(error_msg)
        
        self.app.after(50, self.check_gui_queue)

    # ==================== RESET AND CLEANUP ====================
    
    def reset_form(self):
        """Comprehensive reset of all fields and state."""
        if self.sending_thread and self.sending_thread.is_alive():
            self.update_log("Cannot reset form while emails are being sent.")
            messagebox.showwarning("Warning", "Cannot reset form while emails are being sent.")
            return

        # Stop any ongoing sending
        self.stop_sending()
        self.pause_event.clear()
        self.stop_event.clear()

        # Reset all entry fields
        for widget in [self.subject_entry, self.sender_name_entry, self.sender_email_entry,
                       self.sender_password_entry, self.to_entry, self.emails_per_batch,
                       self.timer_entry, self.auto_pause_entry, self.unsubscribe_entry]:
            widget.delete(0, END)
        
        self.unsubscribe_entry.insert(0, "https://example.com/unsubscribe")
        self.timer_entry.insert(0, str(self.config['default_timer']))

        # Reset textboxes
        for textbox in [self.body_textbox, self.html_textbox, self.tester_recipient_textbox, self.recipient_textbox]:
            textbox.configure(state='normal')
            textbox.delete("1.0", END)
            if textbox in [self.tester_recipient_textbox, self.recipient_textbox]:
                textbox.configure(state='disabled')

        # Reset labels and paths
        for label in [self.recipient_label, self.file_label, self.smtp_label, self.text_subject_label]:
            label.configure(text="")
        
        self.csv_file_path = None
        self.text_file_path = None
        self.text_subject_path = None
        self.sender_csv_file_path = None
        self.gmail_credentials_path = None

        # Reset buttons and attachments
        self.remove_file_button.place_forget()
        self.remove_smtp_button.place_forget()
        self.attachments = []
        self.image_label.configure(image="")
        self.image_photo = None

        # Reset counters and progress
        with self.sent_emails_lock:
            self.sent_emails.clear()
        self.emails_sent = 0
        self.total_emails = 0
        self.progress_bar.set(0)
        self.progress_label.configure(text="Progress: 0 / 0")

        # Reset sender-related
        with self.sender_accounts_lock:
            self.sender_accounts = []
            self.replacement_senders = []
            self.failed_senders = []
        self.sender_logs.clear()
        with self.sender_progress_lock:
            self.sender_progress.clear()
        self.sender_recipient_lists.clear()
        with self.selected_emails_lock:
            self.selected_emails.clear()

        # Reset vars
        self.subject_var.set("Subjects")
        self.format_var.set("HTML")
        self.send_mode_var.set("Multiple SMTP")
        self.actions_var.set("MANUAL")
        self.select_all_var.set(False)
        self.random_pause_var.set(False)
        self.auto_pause_var.set(False)
        self.include_unsubscribe_var.set(False)
        self.random_name_var.set(False)

        # Close all preview windows
        for popup in self.image_preview_windows[:]:
            self.close_preview_popup(popup)
        self.image_preview_windows.clear()

        # Clear log and update
        self.clear_log()
        self.update_log("Full form reset completed.")

        # Reset button states
        self.send_button.configure(text="Send Email", fg_color="blue", state=NORMAL)
        self.pause_button.configure(text="Pause Sending", fg_color="#1A8B53")
        self.stop_button.place_forget()
        
        # Reset status
        self.status_label.configure(text="Inbox impact starts with you")

        # Update log window if open
        if hasattr(self, 'log_window') and self.log_window and self.log_window.winfo_exists():
            self.update_log_display()
        
        # Delete progress state file
        if os.path.exists('progress_state.json'):
            try:
                os.remove('progress_state.json')
            except:
                pass

# ==================== MAIN EXECUTION ====================

if __name__ == "__main__":
    from logging.handlers import RotatingFileHandler
    
    # Setup logging with rotation
    log_handler = RotatingFileHandler(
        'activity.log', 
        maxBytes=10*1024*1024,  # 10MB
        backupCount=5
    )
    log_handler.setFormatter(logging.Formatter(
        '%(asctime)s - %(levelname)s - %(message)s'
    ))
    
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    logger.addHandler(log_handler)
    
    # Create and run app
    app = ctk.CTk()
    email_blaster = Devon(app)
    
    # Handle window close
    def on_closing():
        if email_blaster.sending_thread and email_blaster.sending_thread.is_alive():
            if messagebox.askokcancel("Quit", "Emails are being sent. Do you want to stop and quit?"):
                email_blaster.stop_sending()
                time.sleep(1)  # Give threads time to stop
                app.destroy()
        else:
            app.destroy()
    
    app.protocol("WM_DELETE_WINDOW", on_closing)
    
    print("MAIL_STORM v2.5 - Email Marketing Tool")
    print("=======================================")
    print("Starting application...")
    
    app.mainloop()                    