import tkinter as tk
import random
import string
import json
import os
import requests
from bs4 import BeautifulSoup
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.neighbors import NearestNeighbors
from tkinter import messagebox, ttk
from collections import defaultdict, deque
from threading import Thread
from queue import Queue
from PIL import Image, ImageTk
# Add these imports at the top of the file
import math
import time
from heapq import heappush, heappop
import logging
logging.basicConfig(filename='word_usage.log', level=logging.INFO)
from scipy.sparse import csr_matrix

# Configuration
INITIAL_GRID_SIZE = 5
MAX_GRID_SIZE = 16
GRID_INCREMENT = 1
MAX_LEVELS = 20
WORD_DATA_DIR = "word_data"
THESAURUS_FILE = os.path.join(WORD_DATA_DIR, "thesaurus.json")
WORD_VECTORS_FILE = os.path.join(WORD_DATA_DIR, "word_vectors.json")
SYNONYM_CACHE_FILE = os.path.join(WORD_DATA_DIR, "synonym_cache.json")

from io import BytesIO
import urllib.request

# Pexels API configuration
PEXELS_API_KEY = "1G7j37JNPE8zBh60twM0IqEdyOH4Op5ET3VRo6OQqSY2wPXrCaB3Ei3p"
PEXELS_BASE_URL = "https://api.pexels.com/v1/search"

# Theme to search terms mapping
THEME_IMAGES = {
    'animals': 'wild animals aesthetic',
    'fruits': 'fresh fruits vibrant',
    'countries': 'world landmarks minimal',
    'birds': 'beautiful birds aesthetic',
    'science': 'science lab minimal',
    'chemistry': 'chemistry experiment minimal',
    'art': 'art gallery minimal',
    'mathematics': 'math equations minimal',
    'languages': 'language books aesthetic',
    'history': 'historical places aesthetic minimal'
}
import requests
from io import BytesIO
from urllib.parse import quote

class PexelsImageLoader:
    @staticmethod
    def get_theme_image(theme):
        """Get a random image for the given theme from Pexels"""
        try:
            search_term = THEME_IMAGES.get(theme.lower(), theme)
            encoded_term = quote(search_term)
            url = f"https://api.pexels.com/v1/search"
            
            headers = {
                "Authorization": PEXELS_API_KEY
            }
            
            # In PexelsImageLoader class, modify the search parameters:
            params = {
            "query": search_term,
            "per_page": 10,
            "orientation": "landscape",  # Better fits most screens
            "size": "large"         
            }
            
            # Use requests library instead of urllib for simpler API calls
            response = requests.get(url, headers=headers, params=params)
            
            if response.status_code == 200:
                data = response.json()
                if data.get('photos'):
                    photo = random.choice(data['photos'])
                    image_url = photo['src']['large']
                    
                    # Download the image
                    img_response = requests.get(image_url)
                    if img_response.status_code == 200:
                        return Image.open(BytesIO(img_response.content))
                    else:
                        print(f"Error downloading image: HTTP {img_response.status_code}")
            else:
                print(f"Pexels API error: HTTP {response.status_code}")
                print(f"Response: {response.text}")
                
        except Exception as e:
            print(f"Error loading image from Pexels: {e}")
        
        return None

class ProgressManager:
    """Manages saving and loading game progress"""
    def __init__(self, save_file="user_progress.json"):
        self.save_file = save_file
        # Initialize with default structure for all game modes
        self.progress_data = {
            'single': {'max_level': 1, 'scores': {}, 'grid_sizes': {}, 'themes': {}},
            'two_player': {'max_level': 1, 'scores': {}, 'grid_sizes': {}, 'themes': {}},
            'ai': {'max_level': 1, 'scores': {}, 'grid_sizes': {}, 'themes': {}}
        }
        self.load_progress()
    
    def load_progress(self):
        """Load progress from file if it exists"""
        try:
            if os.path.exists(self.save_file):
                with open(self.save_file, 'r') as f:
                    loaded_data = json.load(f)
                    # Merge loaded data with default structure
                    for mode in ['single', 'two_player', 'ai']:
                        if mode in loaded_data:
                            self.progress_data[mode].update(loaded_data[mode])
            return True
        except Exception as e:
            print(f"Error loading progress: {e}")
            return False
    
    def save_progress(self):
        """Save current progress to file"""
        try:
            os.makedirs(os.path.dirname(self.save_file), exist_ok=True)
            with open(self.save_file, 'w') as f:
                json.dump(self.progress_data, f, indent=2)
            return True
        except Exception as e:
            print(f"Error saving progress: {e}")
            return False
    
    def get_max_unlocked_level(self, game_mode):
        """Get the highest unlocked level for a game mode"""
        if game_mode in self.progress_data:
            return self.progress_data[game_mode].get('max_level', 1)
        return 1
    
    def update_progress(self, game_mode, level, score, grid_size, theme=None):
        """Update progress for a game mode"""
        if game_mode not in self.progress_data:
            self.progress_data[game_mode] = {
                'max_level': 1,
                'scores': {},
                'grid_sizes': {},
                'themes': {}
            }
        
        # Update max unlocked level if this is a new high
        if level > self.progress_data[game_mode]['max_level']:
            self.progress_data[game_mode]['max_level'] = level
        
        # Store level-specific data
        self.progress_data[game_mode]['scores'][str(level)] = score
        self.progress_data[game_mode]['grid_sizes'][str(level)] = grid_size
        if theme:
            self.progress_data[game_mode]['themes'][str(level)] = theme
        
        self.save_progress()
    
    def get_level_data(self, game_mode, level):
        """Get saved data for a specific level"""
        level = str(level)
        if game_mode in self.progress_data:
            return {
                'score': self.progress_data[game_mode]['scores'].get(level, 0),
                'grid_size': self.progress_data[game_mode]['grid_sizes'].get(level, INITIAL_GRID_SIZE),
                'theme': self.progress_data[game_mode]['themes'].get(level, None)
            }
        return {
            'score': 0,
            'grid_size': INITIAL_GRID_SIZE,
            'theme': None
        }
    
    def clear_progress(self, game_mode=None):
        """Clear progress for a specific game mode or all progress"""
        if game_mode:
            if game_mode in self.progress_data:
                del self.progress_data[game_mode]
        else:
            self.progress_data = defaultdict(dict)
        self.save_progress()
        
class App(tk.Tk):
    def __init__(self, *args, **kwargs):
        tk.Tk.__init__(self, *args, **kwargs)
        
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        container = tk.Frame(self)
        container.pack(side="top", fill="both", expand=True)
        container.grid_rowconfigure(0, weight=1)
        container.grid_columnconfigure(0, weight=1)
        
        self.frames = {}
        
        for F in (StartPage, ThemeSelectPage, LevelSelectPage, GamePage):
            frame = F(container, self)
            self.frames[F] = frame
            frame.grid(row=0, column=0, sticky="nsew")
        
        self.show_frame(StartPage)
        
    def on_close(self):
        """Handle window close event"""
        # Save progress before closing
        if GamePage in self.frames:
            game_page = self.frames[GamePage]
            game_page.save_progress()
        self.destroy()
    
    def show_frame(self, cont):
        """Show a frame for the given page class"""
        frame = self.frames[cont]
        frame.tkraise()

class LevelSelectPage(tk.Frame):
    def __init__(self, parent, controller):
        tk.Frame.__init__(self, parent)
        self.controller = controller
        self.game_mode = None
        self.theme = None
        
        self.configure(bg="#f0f4f8")
        
        title = tk.Label(self, text="Select Level", font=("Arial", 24), bg="#f0f4f8", fg="#374785")
        title.pack(pady=20)
        
        self.level_frame = tk.Frame(self, bg="#f0f4f8")
        self.level_frame.pack()
        
        # Create 20 level buttons (4 rows x 5 columns)
        self.level_buttons = []  # This should be a list to maintain order
        for i in range(1, 21):
            btn = tk.Button(
                self.level_frame,
                text=str(i),
                width=4,
                height=2,
                font=("Arial", 12),
                bg="#70c1b3",
                fg="#f8f4ff",
                command=lambda l=i: self.start_level(l)
            )
            row = (i-1)//5
            col = (i-1)%5
            btn.grid(row=row, column=col, padx=5, pady=5)
            self.level_buttons.append(btn)  # Store button in list
        
        back_btn = tk.Button(
            self,
            text="Back",
            font=("Arial", 12),
            command=lambda: controller.show_frame(StartPage)
        )
        back_btn.pack(pady=20)

    def update_buttons(self):
        """Enable/disable level buttons based on progress"""
        game_page = self.controller.frames[GamePage]
        max_unlocked = game_page.progress_manager.get_max_unlocked_level(self.game_mode)
        
        # Ensure level_buttons is a list of widgets
        if not isinstance(self.level_buttons, list):
            self.level_buttons = []
            return
            
        for i, btn in enumerate(self.level_buttons):
            if not isinstance(btn, tk.Widget):  # Skip if not a widget
                continue
                
            level_num = i + 1
            if level_num <= max_unlocked:
                btn.config(state=tk.NORMAL, bg='#70c1b3', fg='blue')
            else:
                btn.config(state=tk.DISABLED, bg='#cccccc', fg='#666666')

    def set_theme(self, theme):
        """Set the selected theme"""
        self.theme = theme
    
    def set_mode(self, mode):
        """Set the game mode before showing this page"""
        self.game_mode = mode
        self.update_buttons()
    
    
    def start_level(self, level):
        """Handle level selection with level parameter"""
        try:
            self.level_start_time = time.time()
            game_page = self.controller.frames[GamePage]
            game_page.set_mode(self.game_mode)
            game_page.set_theme(self.theme)
            game_page.new_game(level)
            self.controller.show_frame(GamePage)
        except Exception as e:
            print(f"Error starting level: {e}")
            # Fallback to level 1 if there's an error
            game_page.new_game(1)
            self.controller.show_frame(GamePage)

class StartPage(tk.Frame):
    def __init__(self, parent, controller):
        tk.Frame.__init__(self, parent)
        self.controller = controller
        
        self.configure(bg="#f0f4f8")
        
        label = tk.Label(self, 
                        text="Word Hunt Challenge", 
                        font=("Arial", 24), 
                        bg="#f0f4f8", 
                        fg="#374785")
        label.pack(pady=50)
        
        # Game mode buttons frame
        button_frame = tk.Frame(self, bg="#f0f4f8")
        button_frame.pack(pady=20)
        
        # Game mode buttons
        modes = [('SINGLE PLAYER', 'single'),
                ('TWO PLAYER', 'two_player'),
                ('HUMAN VS AI', 'ai')]

        # =======================front page with(single player. human vs ai, two player buttons)=================
        for text, mode in modes:
            btn = tk.Button(
                button_frame, 
                text=text,
                font=("Arial", 14),
                width=15,
                height=2,
                bg="#70c1b3",
                fg='blue',
                command=lambda m=mode: self.select_mode(m)
            )
            btn.pack(pady=10)
    
    def select_mode(self, mode):
        """Select game mode and show theme selection"""
        theme_page = self.controller.frames[ThemeSelectPage]
        theme_page.set_mode(mode)
        self.controller.show_frame(ThemeSelectPage)

    def start_game(self, mode):
        game_page = self.controller.frames[GamePage]
        game_page.set_mode(mode)
        
        # Try to load saved progress first
        progress = game_page.load_progress()
        if progress and progress.get('game_mode') == mode:
            if messagebox.askyesno("Continue?", "Would you like to continue your last game?"):
                game_page.load_game_state(progress)
                self.controller.show_frame(GamePage)
                return
        
        # If no saved progress or user chooses not to continue
        game_page.new_game()
        self.controller.show_frame(GamePage)
        
# class StartPage(tk.Frame):
#     def __init__(self, parent, controller):
#         tk.Frame.__init__(self, parent)
#         self.controller = controller
        
#         label = tk.Label(self, text="Word Hunt Challenge", font=("Arial", 24))
#         label.pack(pady=50)
        
#         # Game mode buttons
#         single_btn = ttk.Button(self, text="Single Player",
#                               command=lambda: self.start_game('single'))
#         single_btn.pack(pady=10)
        
#         two_player_btn = ttk.Button(self, text="Two Player",
#                                    command=lambda: self.start_game('two_player'))
#         two_player_btn.pack(pady=10)
        
#         ai_btn = ttk.Button(self, text="VS AI",
#                            command=lambda: self.start_game('ai'))
#         ai_btn.pack(pady=10)
    
#     def start_game(self, mode):
#         game_page = self.controller.frames[GamePage]
#         game_page.set_game_mode(mode)
        
#         # Try to load saved progress first
#         progress = game_page.load_progress()
#         if progress and progress.get('game_mode') == mode:
#             if messagebox.askyesno("Continue?", "Would you like to continue your last game?"):
#                 game_page.load_game_state(progress)
#                 self.controller.show_frame(GamePage)
#                 return
        
#         # If no saved progress or user chooses not to continue
#         game_page.new_game()
#         self.controller.show_frame(GamePage)
        
class WordBankManager:
    """Handles all word-related operations including storage, retrieval, and similarity"""
    def __init__(self):
        self.word_data = defaultdict(dict)
        self.vectorizer = TfidfVectorizer()
        self.knn_model = None
        self.word_vectors = None
        self.word_list = []
        self.synonym_cache = {}
        self.used_words = set()
        self.used_words_by_theme = defaultdict(set)
        self.global_used_words = set()
        self.word_refresh_threshold = 3  # Lowered threshold for more frequent refreshes
        self.initialize_word_bank()

    
    def initialize_word_bank(self):
        """Initialize or load word bank data"""
        self._ensure_data_directory()
        self._load_or_create_word_data()
        self._load_synonym_cache()
        self._load_word_vectors()  # NEW: Load vectors if available
        self._prepare_ai_models()
        
    def _ensure_data_directory(self):
        """Create data directory if it doesn't exist"""
        if not os.path.exists(WORD_DATA_DIR):
            os.makedirs(WORD_DATA_DIR)
    
    def _load_or_create_word_data(self):
        """Load existing word data or create default data"""
        if os.path.exists(THESAURUS_FILE):
            with open(THESAURUS_FILE, 'r') as f:
                self.word_data = json.load(f)
            self._refresh_some_words()
        else:
            self.word_data = {
                'animals': ['LION', 'TIGER', 'BEAR', 'WOLF', 'SHARK'],
                'fruits': ['APPLE', 'MANGO', 'GRAPE', 'PEACH', 'LEMON'],
                'countries': ['CHINA', 'INDIA', 'ITALY', 'SPAIN', 'JAPAN', 
                             'FRANCE', 'GERMANY', 'BRAZIL', 'CANADA', 'MEXICO',
                             'EGYPT', 'KENYA', 'RUSSIA', 'SWEDEN', 'NORWAY',
                             'GREECE', 'TURKEY', 'ISRAEL', 'QATAR', 'THAILAND'],
                
            }
            self._save_word_data()
            self.scrape_additional_words()

    def _refresh_some_words(self):
        """Refresh a portion of words in each category to maintain variety"""
        for category in self.word_data:
            if len(self.word_data[category]) > 10:  # Only refresh if we have enough words
                # Keep 70% of words, refresh 30%
                keep_count = int(len(self.word_data[category]) * 0.5)
                self.word_data[category] = random.sample(self.word_data[category], keep_count)
        self._save_word_data()
        self.scrape_additional_words()

    
    def scrape_additional_words(self):
        """Web scrape to get more words and synonyms"""
        categories = list(self.word_data.keys())
        scrape_thread = Thread(target=self._perform_scraping, args=(categories,))
        scrape_thread.daemon = True
        scrape_thread.start()
    
    # def _try_free_dictionary_api(self, word):
    # """Get synonyms using Free Dictionary API"""
    # try:
    #     url = f"https://api.dictionaryapi.dev/api/v2/entries/en/{word.lower()}"
    #     headers = {'User-Agent': 'Mozilla/5.0'}
    #     response = requests.get(url, headers=headers, timeout=5)
        
    #     if response.status_code == 200:
    #         data = response.json()
    #         synonyms = set()
            
    #         # Extract synonyms from all definitions
    #         for entry in data:
    #             for meaning in entry.get('meanings', []):
    #                 for definition in meaning.get('definitions', []):
    #                     synonyms.update(syn.lower() for syn in definition.get('synonyms', []))
            
    #         return [s.upper() for s in synonyms if s.isalpha()][:20]  # Return top 20 uppercase synonyms
    #     return []
    # except Exception as e:
    #     print(f"Free Dictionary API error for {word}: {e}")
    #     return []

    def _try_merriam_webster(self, word):
        """Get synonyms using Merriam-Webster Thesaurus API with fallback keys"""
        api_keys = [
            "136a4422-ec98-463f-b083-e6bdbae7e775",  # Key 1
            "f4b7fbb8-4a01-4e13-afe1-adefe9c99cce"   # Key 2
        ]
        
        for key in api_keys:
            try:
                url = f"https://www.dictionaryapi.com/api/v3/references/thesaurus/json/{word.lower()}?key={key}"
                headers = {'User-Agent': 'Mozilla/5.0'}
                response = requests.get(url, headers=headers, timeout=5)
                
                if response.status_code == 200:
                    data = response.json()
                    synonyms = set()
                    
                    # Parse the complex MW API response
                    for entry in data:
                        if isinstance(entry, dict):  # Skip spelling suggestions
                            # Main synonyms
                            if 'meta' in entry and 'syns' in entry['meta']:
                                for syn_group in entry['meta']['syns']:
                                    synonyms.update(s.lower() for s in syn_group)
                            
                            # Additional synonyms from definitions
                            if 'def' in entry:
                                for definition in entry['def']:
                                    if 'sseq' in definition:
                                        for sense in definition['sseq']:
                                            if sense[0][0] == 'sense':
                                                sense_data = sense[0][1]
                                                if 'syn_list' in sense_data:
                                                    for syn_group in sense_data['syn_list']:
                                                        for syn in syn_group:
                                                            if 'wd' in syn:
                                                                synonyms.add(syn['wd'].lower())
                    
                    return [s.upper() for s in synonyms if s.isalpha()][:20]  # Return top 20
                
                elif response.status_code == 403:
                    print(f"Key {key[-4:]}... reached limit")  # Show last 4 chars for security
                    continue  # Try next key
                
            except Exception as e:
                print(f"Merriam-Webster API error with key {key[-4:]}...: {e}")
                continue
        
        return []  # Return empty if all keys fail

    def _get_synonyms_for_word(self, word):
        """Enhanced synonym finder with priority to Merriam-Webster"""
        sources = [
            self._try_merriam_webster,
            lambda w: self._get_local_synonyms(w)  # Wrapped for consistency
        ]
        
        synonyms = set()
        for source in sources:
            if len(synonyms) >= 20:  # Stop if we have enough
                break
                
            try:
                result = source(word)
                if result:
                    synonyms.update(w.upper() for w in result if w.isalpha())
            except Exception as e:
                print(f"Error in {source.__name__}: {e}")
        
        return list(synonyms)[:20]
    
    def _perform_scraping(self, categories):
        """Updated scraping using word-level synonym lookup"""
        for category in categories:
            # First try getting synonyms for the category name itself
            synonyms = self._get_synonyms_for_word(category)
            
            # Then try 3 representative words from the category
            sample_words = random.sample(self.word_data.get(category, []), min(3, len(self.word_data.get(category, []))))
            for word in sample_words:
                if len(synonyms) < 20:  # Only look up more if needed
                    synonyms.extend(self._get_synonyms_for_word(word))
            print(synonyms)
            added_words = []
            for word in set(synonyms):  # Deduplicate
                if (len(word) <= MAX_GRID_SIZE 
                    and word.isalpha() 
                    and word not in self.word_data.get(category, [])):
                    self.add_word(word, category)
                    added_words.append(word)
            
            print(f"Added {len(added_words)} words for {category}")
            
            if added_words:
                self.synonym_cache[category] = added_words[:10]
                self._save_word_data()
                self._save_synonym_cache()
    
    def _save_word_data(self):
        """Save word data to file"""
        with open(THESAURUS_FILE, 'w') as f:
            json.dump(self.word_data, f, indent=2)
    
    def _save_synonym_cache(self):
        """Ensures the synonym cache is saved correctly"""
        try:
            with open(SYNONYM_CACHE_FILE, 'w') as f:
                json.dump(self.synonym_cache, f, indent=2, ensure_ascii=False)
        except Exception as e:
            print(f"Failed to save synonym cache: {e}")

    def _load_synonym_cache(self):
        """Loads synonym cache with error handling"""
        try:
            if os.path.exists(SYNONYM_CACHE_FILE):
                with open(SYNONYM_CACHE_FILE, 'r') as f:
                    self.synonym_cache = json.load(f)
        except Exception as e:
            print(f"Failed to load synonym cache: {e}")
            self.synonym_cache = {}  # Fallback to empty cache
    
    def _prepare_ai_models(self):
        """Saves word vectors for faster reloading"""
        self.word_list = []
        contexts = []
        
        for category, words in self.word_data.items():
            for word in words:
                self.word_list.append(word)
                contexts.append(f"{word} {category}")
        
        if contexts:
            self.word_vectors = self.vectorizer.fit_transform(contexts)
            self.knn_model = NearestNeighbors(n_neighbors=5, metric='cosine')
            self.knn_model.fit(self.word_vectors)
            
            # Save vectors to avoid recomputation
            self._save_word_vectors()

    # def _save_word_vectors(self):
    #     """Saves word vectors to a file"""
    #     try:
    #         if hasattr(self.word_vectors, 'toarray'):
    #             vectors = self.word_vectors.toarray().tolist()
    #             with open(WORD_VECTORS_FILE, 'w') as f:
    #                 json.dump({
    #                     'vectors': vectors,
    #                     'words': self.word_list
    #                 }, f, indent=2)
    #     except Exception as e:
    #         print(f"Failed to save word vectors: {e}")


    def _save_word_vectors(self):
        """Saves word vectors in a reconstructable format"""
        try:
            if hasattr(self.word_vectors, 'tocsr'):
                csr = self.word_vectors.tocsr()
                save_data = {
                    'format': 'csr',  # Version identifier
                    'words': self.word_list,
                    'data': csr.data.tolist(),
                    'indices': csr.indices.tolist(),
                    'indptr': csr.indptr.tolist(),
                    'shape': list(csr.shape)  # Store as list [n_rows, n_cols]
                }
                with open(WORD_VECTORS_FILE, 'w') as f:
                    json.dump(save_data, f)
        except Exception as e:
            print(f"Failed to save word vectors: {e}")

    def _load_word_vectors(self):
        """Loads word vectors with proper error handling"""
        try:
            if os.path.exists(WORD_VECTORS_FILE):
                with open(WORD_VECTORS_FILE, 'r') as f:
                    data = json.load(f)
                
                # Check if the format is correct
                if data.get('format') == 'csr':
                    self.word_list = data['words']
                    # Reconstruct CSR matrix
                    self.word_vectors = csr_matrix(
                        (np.array(data['data']),
                        np.array(data['indices']),
                        np.array(data['indptr'])),
                        shape=tuple(data['shape'])
                    )
                    # Rebuild KNN model
                    self.knn_model = NearestNeighbors(n_neighbors=5, metric='cosine')
                    self.knn_model.fit(self.word_vectors)
                    return
                
                # Legacy format handling (if you have old files)
                if 'vectors' in data and isinstance(data['vectors'], list):
                    print("Converting legacy vector format...")
                    self.word_vectors = csr_matrix(np.array(data['vectors']))
                    self._save_word_vectors()  # Resave in new format
                    return
                    
        except Exception as e:
            print(f"Failed to load word vectors: {e}")
        
        # Fallback to recomputing if loading fails
        print("Recomputing word vectors...")
        self._prepare_ai_models()
            
    # def _load_word_vectors(self):
    #     """Loads precomputed word vectors if available"""
    #     try:
    #         if os.path.exists(WORD_VECTORS_FILE):
    #             with open(WORD_VECTORS_FILE, 'r') as f:
    #                 data = json.load(f)
    #                 self.word_list = data['words']
    #                 self.word_vectors = csr_matrix(data['vectors'])
    #                 self.knn_model = NearestNeighbors(n_neighbors=5, metric='cosine')
    #                 self.knn_model.fit(self.word_vectors)
    #     except Exception as e:
    #         print(f"Failed to load word vectors: {e}")
    #         # Fallback to recomputing
    #         self._prepare_ai_models()
    
    def get_similar_words(self, word, category=None, n=5):
        """Get similar words using multiple methods"""
        similar_words = self._get_cached_synonyms(word, category)
        similar_words.extend(self._get_knn_similar_words(word))
        
        if len(similar_words) < n:
            similar_words.extend(self._local_search_related_words(word, n - len(similar_words)))
        
        return similar_words[:n]
    
    def _get_cached_synonyms(self, word, category):
        """Get similar words from cache"""
        if category in self.synonym_cache:
            return [w for w in self.synonym_cache[category] if w != word and w in self.word_list]
        return []
    
    def _get_knn_similar_words(self, word):
        """Get similar words using KNN"""
        if word in self.word_list:
            idx = self.word_list.index(word)
            distances, indices = self.knn_model.kneighbors(self.word_vectors[idx])
            return [self.word_list[i] for i in indices[0] if self.word_list[i] != word]
        return []
    
    def _local_search_related_words(self, word, n):
        """Find related words using local search"""
        related = []
        prefix = word[:2]
        suffix = word[-2:]
        
        for w in self.word_list:
            if w != word and (w.startswith(prefix) or w.endswith(suffix)):
                related.append(w)
                if len(related) >= n:
                    break
        return related
    
    
    def mark_words_used(self, words, category):
        """Add words to the used words sets with immediate save"""
        if isinstance(words, (list, set)):
            words = set(words)
        elif isinstance(words, str):
            words = {words}
            
        words = {str(w).upper() for w in words}
        
        self.used_words_by_theme[category].update(words)
        self.global_used_words.update(words)
        
        # Immediate save to maintain state
        self._save_word_data()
        
        # Check if we need to refresh this category
        if len(self.used_words_by_theme[category]) > self.word_refresh_threshold:
            Thread(target=self._refresh_category_words, args=(category,)).start()
            
    def get_category_words(self, category, max_length=None):
        """Get unused words from a specific category with improved fallback"""
        # First try getting words from the category
        words = self.word_data.get(category, [])
        
        # Filter by length if specified
        if max_length:
            words = [w for w in words if len(w) <= max_length]
            
        # Get used words for this category
        used_words = self.used_words_by_theme[category].union(self.global_used_words)
        
        # Available words are those not used
        available_words = [w for w in words if w not in used_words]
        
        # If we're running low, try to get more words
        if len(available_words) < 10:
            self.reset_used_words(category)
            available_words = [w for w in words if w not in used_words]
            # Reset used words for this category if threshold reached
            if len(self.used_words_by_theme[category]) > self.word_refresh_threshold:
                self.reset_used_words(category)
                available_words = [w for w in words if w not in self.used_words_by_theme[category]]
            
            # If still not enough, use fallback words
            if len(available_words) < 3:
                Thread(target=self._refresh_category_words, args=(category,)).start()
                available_words = self._get_fallback_words(category, max_length)
                
                # Mark fallback words as used to prevent repetition
                self.mark_words_used(available_words, category)
        
        return available_words[:15] 

    def _refresh_category_words(self, category):
        """Background refresh of words for a specific category"""
        if category in self.word_data:
            # Remove some used words to make room for new ones
            self.used_words_by_theme[category] = set()
            
            # Add new words from scraping
            self.scrape_additional_words()
            self._prepare_ai_models()

    def reset_used_words(self, category=None):
        """Clear used words, either for specific category or globally"""
        if category:
            self.used_words_by_theme[category] = set()
        else:
            self.used_words_by_theme = defaultdict(set)
            self.global_used_words = set()

    def _get_fallback_words(self, category, max_length=None):
        """Provide fallback words when none are available"""
        fallback_words = {
            'animals': ['LION', 'TIGER', 'BEAR', 'WOLF', 'SHARK', 'ELEPHANT', 'GIRAFFE', 'ZEBRA'],
            'fruits': ['APPLE', 'ORANGE', 'BANANA', 'GRAPE', 'MANGO', 'PEACH', 'PEAR', 'KIWI'],
            'countries': ['CHINA', 'INDIA', 'ITALY', 'SPAIN', 'JAPAN', 'FRANCE', 'GERMANY', 'BRAZIL',
                         'CANADA', 'MEXICO', 'EGYPT', 'KENYA', 'RUSSIA', 'SWEDEN', 'NORWAY',
                         'GREECE', 'TURKEY', 'ISRAEL', 'QATAR', 'THAILAND'],
            'default': ['WORD', 'GAME', 'PLAY', 'FIND', 'GRID', 'HUNT', 'LETTER', 'PUZZLE']
        }
        
        words = fallback_words.get(category.lower(), fallback_words['default'])
        if max_length:
            words = [w for w in words if len(w) <= max_length]
        return words[:20]  # Return up to 20 fallback words
    
    

    def get_available_categories(self):
        """Return list of all available categories"""
        return list(self.word_data.keys())
    
    
    
    def get_random_category(self):
        """Get a random category"""
        return random.choice(list(self.word_data.keys()))
    
    def add_word(self, word, category):
        """Add a new word to the word bank"""
        word = word.upper().strip()
        if not word.isalpha():
            return False
            
        if category not in self.word_data:
            self.word_data[category] = []
        
        if word not in [w.upper() for w in self.word_data[category]]:
            self.word_data[category].append(word)
            self._save_word_data()
            Thread(target=self._prepare_ai_models).start()
            return True
        return False

class ThemeSelectPage(tk.Frame):
    def __init__(self, parent, controller):
        tk.Frame.__init__(self, parent)
        self.controller = controller
        self.game_mode = None
        
        self.configure(bg="#f0f4f8")
        
        title = tk.Label(self, 
                        text="Select Theme", 
                        font=("Arial", 24), 
                        bg="#f0f4f8", 
                        fg="#374785")
        title.pack(pady=20)
        
        # Theme buttons frame
        theme_frame = tk.Frame(self, bg="#f0f4f8")
        theme_frame.pack(pady=20)
        
        # Theme buttons
        themes = ["Animals", "Fruits", "Countries", "Random"]
        for i, theme in enumerate(themes):
            btn = tk.Button(
                theme_frame,
                text=theme,
                font=("Arial", 14),
                width=15,
                height=2,
                bg="#70c1b3",
                fg="green",
                command=lambda t=theme.lower(): self.select_theme(t)
            )
            btn.grid(row=i//2, column=i%2, padx=10, pady=10)
        
        back_btn = tk.Button(
            self,
            text="Back",
            font=("Arial", 12),
            command=lambda: controller.show_frame(StartPage)
        )
        back_btn.pack(pady=20)
    
    def set_mode(self, mode):
        """Set the game mode from previous page"""
        self.game_mode = mode
    
    def select_theme(self, theme):
        """Handle theme selection and proceed to level selection"""
        level_page = self.controller.frames[LevelSelectPage]
        level_page.set_mode(self.game_mode)
        level_page.set_theme(theme)
        self.controller.show_frame(LevelSelectPage)

class WordGrid:
    """Represents the game grid with words"""
    def __init__(self, size, level, word_bank, theme=None):  # Add theme parameter
        self.size = min(size, MAX_GRID_SIZE)
        self.level = level
        self.word_bank = word_bank
        self.theme = theme  # Store the theme
        self.grid = [[' ' for _ in range(self.size)] for _ in range(self.size)]
        self.words = []
        self.placed_words = []
        self.word_paths = {}
        
        self.generate_grid()
    
    
    def generate_grid(self):
        """Generate grid with improved word selection"""
        category = self.theme if self.theme else self.word_bank.get_random_category()
        
        # Calculate number of words based on level (minimum 3, maximum grid size)
        num_words = min(self.size, max(3, 3 + (self.level // 2)))
        
        # Get words with multiple attempts
        attempts = 0
        while attempts < 3:
            words = self.word_bank.get_category_words(category, self.size)
            if len(words) >= num_words:
                break
            attempts += 1
            self.word_bank.reset_used_words(category)  # Reset if not enough words
        
        # Final fallback if still not enough words
        if len(words) < num_words:
            words = self.word_bank._get_fallback_words(category, self.size)
        
        # Select words using enhanced heuristic
        self.words = self._select_words_heuristically(words, num_words)
        
        # Mark these words as used
        self.word_bank.mark_words_used(set(self.words), category)
        
        self.place_words()
        self.fill_empty_spaces()
        
    def _select_words_heuristically(self, word_list, num_words):
        """Select words using heuristic scoring"""
        if not word_list or num_words <= 0:
            return []
            
        # Score words based on multiple factors
        scored_words = []
        for word in word_list:
            score = 0
            
            # Length score (prefer medium-length words)
            word_len = len(word)
            if 4 <= word_len <= 8:
                score += 3
            elif word_len > 8:
                score += 1
            else:
                score += 2
                
            # Theme word bonus (if we have a theme)
            if hasattr(self, 'current_theme') and self.current_theme:
                # Higher score for words that match the theme
                score += 2
                
            # Letter diversity score
            unique_letters = len(set(word))
            score += unique_letters / len(word)
            
            # Common letter bonus
            common_letters = {'E', 'T', 'A', 'O', 'I', 'N', 'S', 'H', 'R', 'D', 'L', 'C'}
            common_count = sum(1 for c in word if c in common_letters)
            score += common_count / len(word)
            
            scored_words.append((word, score))
        
        # Sort by score and select top words
        scored_words.sort(key=lambda x: -x[1])
        return [w[0] for w in scored_words[:num_words]]
    
    def place_words(self):
        """Place words on the grid"""
        directions = [(1, 0), (0, 1), (1, 1), (1, -1)]
        
        for word in self.words:
            placed = False
            attempts = 0
            
            while not placed and attempts < 100:
                direction = random.choice(directions)
                max_row = self.size - len(word) if direction[0] == 1 else self.size - 1
                max_col = self.size - len(word) if direction[1] == 1 else (
                    len(word) - 1 if direction[1] == -1 else self.size - 1
                )
                
                if max_row < 0 or max_col < 0:
                    attempts += 1
                    continue
                
                row = random.randint(0, max_row)
                col = random.randint(0, max_col)
                
                if self.can_place_word(word, row, col, direction):
                    path = []
                    for i in range(len(word)):
                        r = row + direction[0] * i
                        c = col + direction[1] * i
                        self.grid[r][c] = word[i]
                        path.append((r, c))
                    
                    self.placed_words.append(word)
                    self.word_paths[word] = path
                    placed = True
                
                attempts += 1
    
    def can_place_word(self, word, row, col, direction):
        """Check if word can be placed at given position"""
        for i in range(len(word)):
            r = row + direction[0] * i
            c = col + direction[1] * i
            
            if not (0 <= r < self.size and 0 <= c < self.size):
                return False
                
            if self.grid[r][c] != ' ' and self.grid[r][c] != word[i]:
                return False
                
        return True
    
    def find_word_path(self, word):
        """Find path of a word in the grid"""
        directions = [(1,0),(0,1),(-1,0),(0,-1),(1,1),(1,-1),(-1,1),(-1,-1)]
        
        def dfs(r, c, index, path):
            if index == len(word):
                return path
                
            if not (0 <= r < self.size and 0 <= c < self.size):
                return None
                
            if self.grid[r][c] != word[index]:
                return None
                
            for dr, dc in directions:
                new_path = path + [(r, c)]
                result = dfs(r + dr, c + dc, index + 1, new_path)
                if result:
                    return result
                    
            return None
        
        for i in range(self.size):
            for j in range(self.size):
                if self.grid[i][j] == word[0]:
                    path = dfs(i, j, 0, [])
                    if path:
                        return path
        return None
    
    def fill_empty_spaces(self):
        """Fill empty spaces with random letters"""
        for i in range(self.size):
            for j in range(self.size):
                if self.grid[i][j] == ' ':
                    self.grid[i][j] = random.choice(string.ascii_uppercase)

class LevelManager:
    """Manages game levels and progression"""
    def __init__(self, word_bank):
        self.word_bank = word_bank
        self.level = 1
        self.score = 0
        self.grid_size = INITIAL_GRID_SIZE
        self.current_grid = None
        self.current_theme = None  # Add current theme
    
    def start_level(self):
        """Start a new level"""
        self.current_grid = WordGrid(self.grid_size, self.level, self.word_bank, self.current_theme)
        return self.current_grid
    
    def level_complete(self):
        """Handle level completion"""
        bonus = self.grid_size * 20
        self.score += bonus
        
        if self.level >= MAX_LEVELS:
            return False
        
        if self.level % 3 == 0 and self.grid_size < MAX_GRID_SIZE:
            self.grid_size += GRID_INCREMENT
            
        self.level += 1
        return True
    
    def reset(self):
        """Reset game to initial state"""
        # self.level = 1
        # self.score = 0
        # self.grid_size = INITIAL_GRID_SIZE
        # self.current_grid = None
        self.word_bank.reset_used_words()  # Reset used words


class AIPlayer:
    """AI player that can compete against humans"""
    def __init__(self, word_bank):
        self.word_bank = word_bank
        self.difficulty = 1
        self.score = 0  # Track AI score
        self.search_time_limit = 2.0
        self.search_depth_limit = 3
        self.progress_manager = ProgressManager(os.path.join(WORD_DATA_DIR, "user_progress.json"))
        self.progress_manager.load_progress()
    
    def make_move(self, grid):
        """Make a move based on current grid state"""
        if not grid.placed_words:
            return None
        
        # Different strategies based on difficulty
        if self.difficulty < 3:
            # Easy: random word
            return random.choice(grid.placed_words)
        elif self.difficulty < 5:
            # Medium: longest word
            return max(grid.placed_words, key=len)
        else:
            # Hard: uses word similarity for better choices
            category = self.word_bank.get_random_category()
            for word in sorted(grid.placed_words, key=len, reverse=True):
                similar = self.word_bank.get_similar_words(word, category, 1)
                if similar and similar[0] in grid.placed_words:
                    return similar[0]
            return max(grid.placed_words, key=len)
    
   

    def heuristic_search(self, grid):
        """Enhanced heuristic search for word selection"""
        if not grid.placed_words:
            return None
            
        # Score words based on multiple heuristic factors
        scored_words = []
        for word in grid.placed_words:
            score = 0
            
            # Base score from word length
            score += len(word) * 2
            
            # Letter position bonus (edges are better)
            path = grid.word_paths[word]
            for r, c in path:
                if r == 0 or r == grid.size-1 or c == 0 or c == grid.size-1:
                    score += 1
                    
            # Intersection bonus (words that cross others)
            cross_count = sum(1 for other_word in grid.placed_words 
                             if word != other_word and 
                             set(grid.word_paths[word]) & set(grid.word_paths[other_word]))
            score += cross_count * 0.5
            
            # Difficulty adjustment
            score *= (1 + self.difficulty * 0.2)
            
            scored_words.append((word, score))
        
        # Select word with highest score
        scored_words.sort(key=lambda x: -x[1])
        return scored_words[0][0]
        
    
    def adjust_difficulty(self, level_or_grid):
            """Adjust AI difficulty based on level or grid state"""
            if isinstance(level_or_grid, int):
                # Handle level-based adjustment
                level = level_or_grid
                self.difficulty = min(level // 3, 3)
            else:
                # Handle grid-based adjustment
                grid = level_or_grid
                if grid and hasattr(grid, 'placed_words') and grid.placed_words:
                    avg_word_len = sum(len(w) for w in grid.placed_words) / len(grid.placed_words)
                    self.difficulty = min(int(avg_word_len // 3), 3)
                else:
                    self.difficulty = 1
            
            return self.difficulty
        
    
    def random_strategy(self, grid):
        """Easy: random word"""
        return random.choice(grid.placed_words)
    
    def bfs_strategy(self, grid):
        """Breadth-First Search for optimal path"""
        start_time = time.time()
        best_word = None
        max_length = 0
        
        # BFS queue: (current_word, remaining_words)
        queue = deque()
        queue.append((None, grid.placed_words.copy()))
        
        while queue and time.time() - start_time < self.search_time_limit:
            current, remaining = queue.popleft()
            
            if current and len(current) > max_length:
                best_word = current
                max_length = len(current)
                
            for word in remaining:
                new_remaining = remaining.copy()
                new_remaining.remove(word)
                queue.append((word, new_remaining))
        
        return best_word if best_word else random.choice(grid.placed_words)
    
    def dfs_strategy(self, grid):
        """Depth-First Search with depth limit"""
        start_time = time.time()
        best_word = None
        max_length = 0
        
        # DFS stack: (current_word, remaining_words, depth)
        stack = [(None, grid.placed_words.copy(), 0)]
        
        while stack and time.time() - start_time < self.search_time_limit:
            current, remaining, depth = stack.pop()
            
            if current and len(current) > max_length:
                best_word = current
                max_length = len(current)
                
            if depth < self.search_depth_limit:
                for word in remaining:
                    new_remaining = remaining.copy()
                    new_remaining.remove(word)
                    stack.append((word, new_remaining, depth + 1))
        
        return best_word if best_word else random.choice(grid.placed_words)
    
    def hill_climbing_strategy(self, grid):
        """Hill Climbing with random restarts"""
        start_time = time.time()
        best_word = max(grid.placed_words, key=len)
        best_score = len(best_word)
        restarts = 0
        
        while time.time() - start_time < self.search_time_limit and restarts < 3:
            current = random.choice(grid.placed_words)
            current_score = len(current)
            improved = True
            
            while improved and time.time() - start_time < self.search_time_limit:
                improved = False
                neighbors = self.get_similar_words(current, grid.placed_words)
                
                for neighbor in neighbors:
                    neighbor_score = len(neighbor)
                    if neighbor_score > current_score:
                        current = neighbor
                        current_score = neighbor_score
                        improved = True
                        break
                
                if current_score > best_score:
                    best_word = current
                    best_score = current_score
            
            restarts += 1
        
        return best_word
    
    def minimax_strategy(self, grid):
        """Minimax with Alpha-Beta Pruning"""
        start_time = time.time()
        best_word = None
        best_value = -math.inf
        alpha = -math.inf
        beta = math.inf
        
        # Evaluate each possible move
        for word in grid.placed_words:
            if time.time() - start_time >= self.search_time_limit:
                break
                
            # Simulate taking this word
            new_remaining = [w for w in grid.placed_words if w != word]
            value = self.minimax(new_remaining, False, alpha, beta, 
                               depth=1, start_time=start_time)
            
            if value > best_value:
                best_value = value
                best_word = word
                alpha = max(alpha, best_value)
        
        return best_word if best_word else random.choice(grid.placed_words)
    
    def minimax(self, remaining_words, is_maximizing, alpha, beta, depth, start_time):
        """Minimax recursive helper with alpha-beta pruning"""
        if (time.time() - start_time >= self.search_time_limit or 
            depth >= self.search_depth_limit or 
            not remaining_words):
            return self.evaluate_state(remaining_words, is_maximizing)
        
        if is_maximizing:
            value = -math.inf
            for word in remaining_words:
                new_remaining = [w for w in remaining_words if w != word]
                value = max(value, self.minimax(new_remaining, False, alpha, beta, 
                                              depth + 1, start_time))
                alpha = max(alpha, value)
                if alpha >= beta:
                    break  # Beta cutoff
            return value
        else:
            value = math.inf
            for word in remaining_words:
                new_remaining = [w for w in remaining_words if w != word]
                value = min(value, self.minimax(new_remaining, True, alpha, beta, 
                                              depth + 1, start_time))
                beta = min(beta, value)
                if alpha >= beta:
                    break  # Alpha cutoff
            return value
    
    def evaluate_state(self, remaining_words, is_maximizing):
        """Evaluation function for minimax"""
        if not remaining_words:
            return 100 if is_maximizing else -100
            
        # Score based on word lengths and counts
        avg_length = sum(len(w) for w in remaining_words) / len(remaining_words)
        count = len(remaining_words)
        
        # Favor states with fewer long words for maximizer
        return (1/avg_length) * 50 - count * 5
    
    def get_similar_words(self, word, word_list):
        """Get similar words from the current word list"""
        similar = []
        prefix = word[:2]
        suffix = word[-2:]
        
        for w in word_list:
            if w != word and (w.startswith(prefix) or w.endswith(suffix)):
                similar.append(w)
        
        # Add some random words to diversify
        if len(similar) < 3:
            similar.extend(random.sample(word_list, min(3, len(word_list))))
        
        return similar

class TwoPlayerGame:
    def __init__(self, word_bank):
        self.word_bank = word_bank
        self.scores = {1: 0, 2: 0}
        self.level = 1
        self.grid_size = INITIAL_GRID_SIZE  # Add this
        self.current_theme = None
        self.current_player = 1  # Initialize to player 1
        self.current_grid = None  # Add this
        self.progress_manager = ProgressManager(os.path.join(WORD_DATA_DIR, "user_progress.json"))
        self.progress_manager.load_progress()
    
    
    def set_theme(self, theme):
        """Set the current theme for word selection"""
        self.current_theme = theme
    
    def start_level(self):
        self.level_start_time = time.time()
        self.word_bank.reset_used_words()  # Reset used words
        print(f"Starting two-player level with theme: {self.current_theme}")  # Debug print
        self.current_grid = WordGrid(
            self.grid_size, 
            self.level, 
            self.word_bank,
            self.current_theme
        )
        return self.current_grid
    
    def make_move(self, player, word):
        """Handle a player's move"""
        if word in self.current_grid.placed_words:
            self.current_grid.placed_words.remove(word)
            self.scores[player] += len(word) * 10
            self.current_player = 2 if player == 1 else 1
            return True
        return False
    
    def level_complete(self):
        """Check if level is complete and handle progression"""
        if not self.current_grid.placed_words:
            if self.level % 3 == 0 and self.grid_size < MAX_GRID_SIZE:
                self.grid_size += GRID_INCREMENT
            self.level += 1
            return True
        return False


# Theme colors dictionary
THEME_COLORS = {
    'animals': {
        'bg': '#f0f8ff',  # Light blue background
        'title': '#1e3d59',  # Dark blue title
        'button': '#43b0f1',  # Medium blue buttons
        'grid': '#e8f4fc',  # Very light blue grid
        'highlight': '#a2d5f2'  # Highlighted cells
    },
    'fruits': {
        'bg': '#fff8f0',  # Light peach background
        'title': '#ff6f3c',  # Orange title
        'button': '#ff9a3c',  # Medium orange buttons
        'grid': '#fce8e8',  # Very light peach grid
        'highlight': '#ffba93'  # Highlighted cells
    },
    'countries': {
        'bg': '#f0fff8',  # Light mint background
        'title': '#1b512d',  # Dark green title
        'button': '#4caf50',  # Medium green buttons
        'grid': '#e8fcf4',  # Very light mint grid
        'highlight': '#a2f2d5'  # Highlighted cells
    },
    'default': {
        'bg': '#f0f4f8',  # Original background
        'title': '#374785',  # Original title
        'button': '#70c1b3',  # Original buttons
        'grid': '#f0f8ff',    # Original grid
        'highlight': '#ace7ef'  # Original highlighted cells
    }
}

class GamePage(tk.Frame):
    def __init__(self, parent, controller):
        tk.Frame.__init__(self, parent)
        self.controller = controller
        self.current_grid = None
        self.current_theme = "default"
        self.selected_theme = None
        self.level_start_time = 0  # Add this line
        self.level_time = 0  
        self.used_words_by_theme = defaultdict(set)
        self.global_used_words = set()
        self.word_refresh_threshold = 5
        self.progress_manager = ProgressManager(os.path.join(WORD_DATA_DIR, "user_progress.json"))
        # Game state variables
        self.game_mode = 'single'
        self.ai_turn = False
        self.starting_level = 1  # Track the level we started at

        self.current_bg_image = None
        self.bg_image_label = None

        self.heuristic_search_depth = 3  # Depth for heuristic search
        self.scraping_sources = [
            "https://www.thesaurus.com/browse/",
            "https://www.merriam-webster.com/thesaurus/",
            "https://www.wordhippo.com/what-is/another-word-for/"
        ]
        
        # Initialize save file path
        self.save_file = os.path.join(WORD_DATA_DIR, "user_progress.json")
        
        # Game components
        self.word_bank = WordBankManager()
        self.level_manager = LevelManager(self.word_bank)
        self.two_player_game = TwoPlayerGame(self.word_bank)
        self.ai_player = AIPlayer(self.word_bank)

        
        # UI Setup
        self.setup_ui()
        
        # Add back button
        self.back_btn = ttk.Button(self, text="Back to Menu",
                                 command=self.return_to_menu)
        self.back_btn.pack(anchor="nw", padx=10, pady=10)

    def heuristic_scrape_words(self, category, max_words=20):
        """Heuristic web scraping with priority-based search"""
        words_found = set()
        queue = deque([(category, 0)])  # (search_term, depth)
        visited = set()
        
        while queue and len(words_found) < max_words:
            search_term, depth = queue.popleft()
            
            if depth > self.heuristic_search_depth:
                continue
                
            if search_term in visited:
                continue
                
            visited.add(search_term)
            
            # Try multiple sources
            for source in self.scraping_sources:
                try:
                    new_words = self._scrape_from_source(source + search_term)
                    
                    for word in new_words:
                        if (word.isalpha() and 
                            word.upper() not in words_found and 
                            len(word) <= MAX_GRID_SIZE):
                            words_found.add(word.upper())
                            
                            # Add related words to queue with higher priority
                            if depth < self.heuristic_search_depth:
                                queue.append((word, depth + 1))
                                
                    if len(words_found) >= max_words:
                        break
                        
                except Exception as e:
                    print(f"Error scraping {source}{search_term}: {e}")
        
        return list(words_found)
    
    def _scrape_from_source(self, url):
        """Scrape words from a specific source with improved parsing"""
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        }
        
        try:
            response = requests.get(url, headers=headers, timeout=10)
            soup = BeautifulSoup(response.text, 'html.parser')
            words = []
            
            # Try multiple parsing strategies
            strategies = [
                self._parse_thesaurus_com,
                self._parse_merriam_webster,
                self._parse_wordhippo
            ]
            
            for strategy in strategies:
                words = strategy(soup)
                if words:
                    break
                    
            return words
            
        except Exception as e:
            print(f"Error scraping {url}: {e}")
            return []
    
    def _parse_thesaurus_com(self, soup):
        """Parse thesaurus.com specific format"""
        words = []
        container = soup.find('div', {'id': 'meanings'})
        if container:
            items = container.find_all('a', {'class': 'css-1kg1yv8 eh475bn0'})
            words = [item.text.strip().upper() for item in items]
        return words
    
    def _parse_merriam_webster(self, soup):
        """Parse merriam-webster.com specific format"""
        words = []
        container = soup.find('div', {'class': 'thesaurus-entry'})
        if container:
            items = container.find_all('a', {'class': 'thesaurus-word'})
            words = [item.text.strip().upper() for item in items]
        return words
    
    def _parse_wordhippo(self, soup):
        """Parse wordhippo.com specific format"""
        words = []
        container = soup.find('div', {'id': 'relatedwords'})
        if container:
            items = container.find_all('div', {'class': 'wordblock'})
            words = [item.text.strip().upper() for item in items]
        return words
    
    def setup_ui(self):
        """Initialize all UI components with modern styling"""
        # Configure style constants
        BG_COLOR = '#f8f9fa'
        PRIMARY_COLOR = '#6c5ce7'
        SECONDARY_COLOR = '#a29bfe'
        ACCENT_COLOR = '#00cec9'
        TEXT_COLOR = '#2d3436'
        LIGHT_TEXT = '#636e72'
        CARD_COLOR = '#ffffff'
        
        # Main frame with modern background
        self.main_frame = tk.Frame(self, bg=BG_COLOR)
        self.main_frame.pack(expand=True, fill=tk.BOTH, padx=20, pady=20)
        
        # Header frame with subtle shadow effect
        self.header_frame = tk.Frame(self.main_frame, bg=BG_COLOR)
        self.header_frame.pack(fill=tk.X, pady=(0, 20))
        
        self.title_label = tk.Label(
            self.header_frame, 
            text="WORD HUNT CHALLENGE", 
            font=('Segoe UI', 24, 'bold'),
            fg='#1e3d59',
            bg=BG_COLOR
        )
        self.title_label.pack(pady=10)
        
        
        
        # Game info panel with card-like appearance
        self.info_frame = tk.Frame(
            self.main_frame, 
            bg=CARD_COLOR,
            padx=15,
            pady=10,
            highlightbackground='#dfe6e9',
            highlightthickness=1
        )
        self.info_frame.pack(fill=tk.X, pady=(0, 20))
        
        info_font = ('Segoe UI', 12)
        
        self.level_label = tk.Label(
            self.info_frame, 
            text=f"Level: 1/{MAX_LEVELS}",
            font=info_font,
            bg=CARD_COLOR,
            fg=TEXT_COLOR
        )
        self.level_label.pack(side=tk.LEFT, padx=10)
        
        tk.Frame(self.info_frame, width=1, bg='#dfe6e9', height=20).pack(side=tk.LEFT, padx=10)
        
        self.score_label = tk.Label(
            self.info_frame, 
            text=f"Score: 0",
            font=info_font,
            bg=CARD_COLOR,
            fg=TEXT_COLOR
        )
        self.score_label.pack(side=tk.LEFT, padx=10)
        
        tk.Frame(self.info_frame, width=1, bg='#dfe6e9', height=20).pack(side=tk.LEFT, padx=10)
        
        self.player_turn_label = tk.Label(
            self.info_frame,
            text="",
            font=info_font,
            bg=CARD_COLOR,
            fg=TEXT_COLOR
        )
        self.player_turn_label.pack(side=tk.RIGHT, padx=10)
        
        # Game grid with card styling
        self.grid_frame = tk.Frame(
            self.main_frame, 
            bg=CARD_COLOR,
            padx=15,
            pady=15,
            highlightbackground='#dfe6e9',
            highlightthickness=1
        )
        self.grid_frame.pack(pady=(0, 20))
        self.cells = []
        
        # Input area with modern styling
        self.input_frame = tk.Frame(self.main_frame, bg=BG_COLOR)
        self.input_frame.pack(fill=tk.X, pady=(0, 20))
        
        self.word_entry = tk.Entry(
            self.input_frame,
            font=('Segoe UI', 16),
            width=20,
            relief='flat',
            bd=2,
            bg=CARD_COLOR,
            fg=TEXT_COLOR,
            highlightcolor=PRIMARY_COLOR,
            highlightbackground='#b2bec3',
            highlightthickness=1
        )
        self.word_entry.pack(side=tk.LEFT, padx=(0, 10), ipady=8)
        self.word_entry.bind('<Return>', lambda e: self.check_word())
        
        # Modern buttons with consistent styling
        button_style = {
            'font': ('Segoe UI', 12, 'bold'),
            'bg': PRIMARY_COLOR,
            'fg': 'blue',
            'activebackground': SECONDARY_COLOR,
            'activeforeground': 'green',
            'bd': 0,
            'relief': 'flat',
            'width': 12,
            'height': 1,
            'cursor': 'hand2',
            'padx': 12,
            'pady': 8
        }
        
        self.submit_btn = tk.Button(
            self.input_frame,
            text="Submit",
            command=self.check_word,
            **button_style
        )
        self.submit_btn.pack(side=tk.LEFT, padx=(0, 10))
        
        self.hint_button = tk.Button(
            self.input_frame,
            text="Hint",
            command=self.give_hint,
            **{**button_style, 'bg': ACCENT_COLOR, 'activebackground': '#00b894'}
        )
        self.hint_button.pack(side=tk.LEFT)
        
        # Back button with modern flat style
        self.back_btn = tk.Button(
            self.main_frame,
            text="← Back to Theme Page",
            command=self.return_to_theme_page,
            font=('Segoe UI', 10),
            fg=LIGHT_TEXT,
            bg=BG_COLOR,
            activeforeground=PRIMARY_COLOR,
            activebackground=BG_COLOR,
            bd=0,
            cursor='hand2'
        )
        self.back_btn.pack(anchor="nw", padx=5, pady=5)
        
        # Initialize game
        self.new_game()

    # Add image processing in load_theme_background():
    def load_theme_background(self, theme):
            if theme == "default":
                # Reset to default colors
                return
                
            image = PexelsImageLoader.get_theme_image(theme)
            if image:
                try:
                    # Apply aesthetic filters
                    from PIL import ImageEnhance, ImageFilter
                    
                    # 1. Blur slightly for better text readability
                    image = image.filter(ImageFilter.GaussianBlur(radius=2))
                    
                    # 2. Darken/Lighten based on theme
                    if theme in ['animals', 'science']:
                        enhancer = ImageEnhance.Brightness(image)
                        # image = enhancer.enhance(0.7)  # Darker
                    else:
                        enhancer = ImageEnhance.Brightness(image)
                        # image = enhancer.enhance(1.1)  # Brighter
                        
                    # # 3. Add overlay for better contrast
                    # overlay = Image.new('RGBA', image.size, (0,0,0,90))  # Black overlay
                    # image = Image.alpha_composite(image.convert('RGBA'), overlay)
                    
                    # Resize
                    window_width = self.winfo_width() or 1000
                    window_height = self.winfo_height() or 700
                    image = image.resize((window_width, window_height), Image.LANCZOS)
                    
                    # Set image
                    self.current_bg_image = ImageTk.PhotoImage(image)
                    
                    # Create or update background image label
                    if not self.bg_image_label:
                        self.bg_image_label = tk.Label(self.main_frame)
                        self.bg_image_label.place(x=0, y=0, relwidth=1, relheight=1)
                        self.bg_image_label.lower()  # Move to back
                    
                    self.bg_image_label.config(image=self.current_bg_image)
                    
                    # Make frames semi-transparent
                    for frame in [self.header_frame,  
                                self.info_frame, self.grid_frame, self.input_frame]:
                        frame.config(bg='#f0f4f8')  # Slightly transparent
                        for widget in frame.winfo_children():
                            try:
                                widget.config(bg='#f0f4f8')  # Slightly transparent
                            except:
                                pass
                except Exception as e:
                    print(f"Error setting background image: {e}")
                    # Fall back to default colors
                    self.main_frame.config(bg='#f0f4f8')
                    if self.bg_image_label:
                        self.bg_image_label.destroy()
                        self.bg_image_label = None

    def return_to_theme_page(self):
        """Save progress and return to theme selection page"""
        if self.game_mode == 'single' or self.game_mode == 'ai':
            self.progress_manager.update_progress(
                self.game_mode,
                self.level_manager.level,
                self.level_manager.score,
                self.level_manager.grid_size,
                self.selected_theme
            )
        elif self.game_mode == 'two_player':
            self.progress_manager.update_progress(
                self.game_mode,
                self.two_player_game.level,
                max(self.two_player_game.scores.values()),
                self.two_player_game.grid_size,
                self.selected_theme
            )
        
        theme_page = self.controller.frames[ThemeSelectPage]
        theme_page.set_mode(self.game_mode)
        self.controller.show_frame(ThemeSelectPage)
        
    def set_theme(self, theme):
        """Set the selected theme for all game modes"""
        self.selected_theme = theme if theme != "random" else None
        
        # Reset used words for this theme when changing
        if self.selected_theme:
            self.word_bank.reset_used_words(self.selected_theme.lower())
        
        # Update the theme for all game managers
        self.level_manager.current_theme = self.selected_theme
        self.two_player_game.current_theme = self.selected_theme
        
        # Load and set background image
        self.load_theme_background(self.selected_theme if self.selected_theme else "default")
    
    def new_game(self, level=1):
        """Start a new game at specified level"""
        try:
            # Get max unlocked level for current game mode
            max_unlocked = self.progress_manager.get_max_unlocked_level(self.game_mode)
            
            # Ensure level is within valid range
            level = max(1, min(level, max_unlocked))
            
            if self.game_mode == 'single':
                self.level_manager.current_theme = self.selected_theme
                self.level_manager.level = level
                level_data = self.progress_manager.get_level_data(self.game_mode, level)
                self.level_manager.grid_size = level_data['grid_size']
                self.level_manager.score = level_data['score']
                self.start_level()
            
            elif self.game_mode == 'two_player':
                self.two_player_game.current_theme = self.selected_theme
                self.two_player_game.level = level
                level_data = self.progress_manager.get_level_data(self.game_mode, level)
                self.two_player_game.grid_size = level_data['grid_size']
                self.start_two_player_level()
            
            elif self.game_mode == 'ai':
                self.level_manager.current_theme = self.selected_theme
                self.level_manager.level = level
                level_data = self.progress_manager.get_level_data(self.game_mode, level)
                self.level_manager.grid_size = level_data['grid_size']
                self.level_manager.score = level_data['score']
                self.ai_player.adjust_difficulty(level)
                self.start_ai_game()
                
        except Exception as e:
            print(f"Error in new_game: {e}")
            # Fallback to basic initialization
            self.level_manager = LevelManager(self.word_bank)
            self.level_manager.level = 1
            self.start_level()
    
    def save_progress(self):
        """Save progress using ProgressManager"""
        if self.game_mode == 'single' or self.game_mode == 'ai':
            self.progress_manager.update_progress(
                self.game_mode,
                self.level_manager.level,
                self.level_manager.score,
                self.level_manager.grid_size,
                self.selected_theme
            )
        elif self.game_mode == 'two_player':
            self.progress_manager.update_progress(
                self.game_mode,
                self.two_player_game.level,
                max(self.two_player_game.scores.values()),
                self.two_player_game.grid_size,
                self.selected_theme
            )
        return True
        
    def return_to_menu(self):
        """Save progress and return to menu"""
        self.save_progress()
        self.controller.show_frame(StartPage)
        
    def load_progress(self):
        """Load progress using ProgressManager"""
        return self.progress_manager.load_progress()
        
    def load_initial_progress(self):
        """Load progress when game first starts"""
        progress = self.load_progress()
        if progress:
            # Ask user if they want to continue
            if messagebox.askyesno("Continue?", "Would you like to continue your last game?"):
                self.load_game_state(progress)
            else:
                # Clear saved progress if they don't want to continue
                self.clear_saved_progress()
    
    def clear_saved_progress(self):
        """Clear the saved progress file"""
        if os.path.exists(self.save_file):
            try:
                os.remove(self.save_file)
            except Exception as e:
                print(f"Error clearing progress: {e}")
    
    
    
    def load_game_state(self, progress):
        """Enhanced load game state method"""
        if not progress:
            return False
            
        try:
            # Set game mode first
            if 'game_mode' in progress:
                self.game_mode = progress['game_mode']
            
            if self.game_mode == 'single' and progress.get('single_player'):
                data = progress['single_player']
                self.level_manager.level = data['current_level']
                self.level_manager.score = data['score']
                self.level_manager.grid_size = data['grid_size']
                self.level_manager.current_theme = data['theme'] if data['theme'] != "default" else None
                self.theme_var.set(data['theme'])
                self.start_level()
                return True
                
            elif self.game_mode == 'two_player' and progress.get('two_player'):
                data = progress['two_player']
                self.two_player_game.level = data['current_level']
                self.two_player_game.scores = {1: data['player1_score'], 2: data['player2_score']}
                self.two_player_game.grid_size = data['grid_size']
                self.two_player_game.current_player = data['current_player']
                self.two_player_game.current_theme = data['theme'] if data['theme'] != "default" else None
                self.theme_var.set(data['theme'])
                self.start_two_player_level()
                return True
                
            elif self.game_mode == 'ai' and progress.get('ai_mode'):
                data = progress['ai_mode']
                self.level_manager.level = data['current_level']
                self.level_manager.score = data['score']
                self.level_manager.grid_size = data['grid_size']
                self.level_manager.current_theme = data['theme'] if data['theme'] != "default" else None
                self.ai_player.difficulty = data['ai_difficulty']
                self.theme_var.set(data['theme'])
                self.start_ai_game()
                return True
                
            return False
        except Exception as e:
            print(f"Error loading game state: {e}")
            return False
    
    
    def create_grid(self, grid_data):
        """Create the game grid UI"""
        for widget in self.grid_frame.winfo_children():
            widget.destroy()
        
        self.cells = []
        for i in range(len(grid_data)):
            row = []
            for j in range(len(grid_data[i])):
                cell = tk.Label(
                    self.grid_frame,
                    text=grid_data[i][j],
                    font=('Comic Sans MS', 20, 'bold'),
                    width=3,
                    height=1,
                    relief='groove',
                    bg=THEME_COLORS[self.current_theme]['grid']
                )
                cell.grid(row=i, column=j, padx=3, pady=3)
                cell.bind('<Button-1>', lambda e, i=i, j=j: self.select_cell(i, j))
                row.append(cell)
            self.cells.append(row)
    
    def select_cell(self, row, col):
        """Handle cell selection"""
        if not hasattr(self, 'selected_cells'):
            self.selected_cells = []
            
        self.selected_cells.append((row, col))
        self.word_entry.insert(tk.END, self.get_grid_cell(row, col))
        self.cells[row][col].config(bg=THEME_COLORS[self.current_theme]['highlight'])
        
        if len(self.selected_cells) > 1:
            self.validate_path()
    
    def validate_path(self):
        """Validate selected path"""
        if len(self.selected_cells) < 2:
            return True
            
        visited = set()
        queue = deque([self.selected_cells[0]])
        target = self.selected_cells[-1]
        
        while queue:
            current = queue.popleft()
            if current == target:
                return True
                
            if current in visited:
                continue
                
            visited.add(current)
            
            for dr, dc in [(1,0),(0,1),(-1,0),(0,-1),(1,1),(1,-1),(-1,1),(-1,-1)]:
                neighbor = (current[0] + dr, current[1] + dc)
                if neighbor in self.selected_cells and neighbor not in visited:
                    queue.append(neighbor)
        
        self.clear_selection()
        return False
    
    def clear_selection(self):
        """Clear selected cells"""
        for row, col in self.selected_cells:
            self.cells[row][col].config(bg=THEME_COLORS[self.current_theme]['grid'])
        self.selected_cells = []
        self.word_entry.delete(0, tk.END)
    
    def highlight_word(self, word, path, player=None):
        """Highlight a found word on the grid"""
        color = '#90ee90'  # Default green
        if player == 1:
            color = '#b3e5fc'  # Player 1 color
        elif player == 2:
            color = '#f8bbd0'  # Player 2 color
            
        for row, col in path:
            self.cells[row][col].config(bg=color)
    
    def update_display(self, level=None, score=None, words_to_find=None, current_player=None):
        """Update game display with optional parameters"""
        # Set default values if None
        if level is None:
            level = self.level_manager.level if hasattr(self, 'level_manager') else 1
            
        if score is None:
            if self.game_mode == 'single':
                score = self.level_manager.score if hasattr(self, 'level_manager') else 0
            elif self.game_mode == 'two_player':
                score = self.two_player_game.scores if hasattr(self, 'two_player_game') else {1:0, 2:0}
            else:  # ai mode
                score = {'Human': getattr(self.level_manager, 'score', 0),
                        'AI': getattr(self.ai_player, 'score', 0)}
                
        if words_to_find is None:
            words_to_find = getattr(self.current_grid, 'placed_words', []) if hasattr(self, 'current_grid') else []

        # Update UI elements
        self.level_label.config(text=f"Level: {level}/{MAX_LEVELS}")
        
        if self.game_mode == 'two_player':
            self.score_label.config(text=f"Player 1: {score.get(1, 0)} | Player 2: {score.get(2, 0)}")
        elif isinstance(score, dict):
            self.score_label.config(text=f"Human: {score.get('Human', 0)} | AI: {score.get('AI', 0)}")
        else:
            self.score_label.config(text=f"Score: {score}")
            
        if current_player:
            self.player_turn_label.config(text=f"Player {current_player}'s Turn")
        
    
    def show_message(self, title, message):
        """Show a message box"""
        messagebox.showinfo(title, message)
    
    def change_theme(self, event=None):
        """Change UI theme and word selection"""
        selected_theme = self.theme_var.get()
        print(f"Generating grid with theme: {selected_theme}")
        self.current_theme = new_theme
        
        # Update theme in game managers
        self.level_manager.current_theme = new_theme if new_theme != "default" else None
        self.two_player_game.set_theme(new_theme)
        
        # Update UI colors
        self.update_theme_colors(new_theme)
        
        # Update theme info display
        if hasattr(self, 'theme_info_label'):
            if new_theme != "default":
                self.theme_info_label.config(text=f"Theme: {new_theme.capitalize()}")
            else:
                self.theme_info_label.config(text="")
        
        # Start new game with selected theme
        self.new_game()

    def handle_level_completion(self):
        """Handle level/game completion for AI vs Human mode"""
        if self.level_manager.level_complete():
            bonus = self.level_manager.grid_size * 20
            self.level_manager.score += bonus
            self.show_message(
                "Level Complete!", 
                f"Bonus: {bonus} points!\n"
                f"Scores:\nHuman: {self.level_manager.score}\nAI: {self.ai_player.score}"
            )
            self.start_level()
        else:
            # Game complete - determine winner
            winner = "Human" if self.level_manager.score > self.ai_player.score else "AI"
            self.show_message(
                "Game Complete!", 
                f"Final Scores:\nHuman: {self.level_manager.score}\n"
                f"AI: {self.ai_player.score}\n{winner} wins!"
            )
            self.controller.show_frame(StartPage)
    
    def update_theme_colors(self, theme):
        """Update all UI elements with new theme colors"""
        colors = THEME_COLORS[theme]
        
        # Update frame backgrounds
        self.main_frame.config(bg=colors['bg'])
        self.header_frame.config(bg=colors['bg'])
        # self.options_frame.config(bg=colors['bg'])
        self.info_frame.config(bg=colors['bg'])
        self.grid_frame.config(bg=colors['bg'])
        self.input_frame.config(bg=colors['bg'])
        
        # Update labels
        self.title_label.config(
            fg=colors['title'],
            bg=colors['bg']
        )
        
        
        
        # Update grid cells if they exist
        if hasattr(self, 'cells'):
            for row in self.cells:
                for cell in row:
                    if cell.cget('bg') not in ['#90ee90', '#b3e5fc', '#f8bbd0']:
                        cell.config(bg=colors['grid'])
    
    # Game control methods (from WordHuntGame)
    def set_mode(self, mode):
        self.game_mode = mode
        self.new_game()
    
    def load_initial_progress(self):
        """Load progress when game first starts"""
        progress = self.load_progress()
        if progress:
            # Ask user if they want to continue
            if messagebox.askyesno("Continue?", "Would you like to continue your last game?"):
                self.load_game_state(progress)
            else:
                # Clear saved progress if they don't want to continue
                self.clear_saved_progress()
    
    def clear_saved_progress(self):
        """Clear the saved progress file"""
        if os.path.exists(self.save_file):
            try:
                os.remove(self.save_file)
            except Exception as e:
                print(f"Error clearing progress: {e}")
    
    def save_progress(self):
        """Enhanced save progress method"""
        progress = {
            "game_mode": self.game_mode,
            "single_player": {
                "current_level": self.level_manager.level,
                "score": self.level_manager.score,
                "grid_size": self.level_manager.grid_size,
                "theme": self.level_manager.current_theme or "default"
            },
            "two_player": {
                "player1_score": self.two_player_game.scores.get(1, 0),
                "player2_score": self.two_player_game.scores.get(2, 0),
                "current_level": self.two_player_game.level,
                "grid_size": self.two_player_game.grid_size,
                "current_player": self.two_player_game.current_player,
                "theme": self.two_player_game.current_theme or "default"
            },
            "ai_mode": {
                "current_level": self.level_manager.level,
                "score": self.level_manager.score,
                "grid_size": self.level_manager.grid_size,
                "theme": self.level_manager.current_theme or "default",
                "ai_difficulty": self.ai_player.difficulty
            }
        }
        
        try:
            # Create directory if it doesn't exist
            os.makedirs(WORD_DATA_DIR, exist_ok=True)
            
            with open(self.save_file, 'w') as f:
                json.dump(progress, f, indent=2)
            return True
        except Exception as e:
            print(f"Error saving progress: {e}")
            return False
    
    def load_game_state(self, progress):
        """Enhanced load game state method"""
        if not progress:
            return False
            
        try:
            # Set game mode first
            if 'game_mode' in progress:
                self.game_mode = progress['game_mode']
            
            if self.game_mode == 'single' and progress.get('single_player'):
                data = progress['single_player']
                self.level_manager.level = data['current_level']
                self.level_manager.score = data['score']
                self.level_manager.grid_size = data['grid_size']
                self.level_manager.current_theme = data['theme'] if data['theme'] != "default" else None
                self.theme_var.set(data['theme'])
                self.start_level()
                return True
                
            elif self.game_mode == 'two_player' and progress.get('two_player'):
                data = progress['two_player']
                self.two_player_game.level = data['current_level']
                self.two_player_game.scores = {1: data['player1_score'], 2: data['player2_score']}
                self.two_player_game.grid_size = data['grid_size']
                self.two_player_game.current_player = data['current_player']
                self.two_player_game.current_theme = data['theme'] if data['theme'] != "default" else None
                self.theme_var.set(data['theme'])
                self.start_two_player_level()
                return True
                
            elif self.game_mode == 'ai' and progress.get('ai_mode'):
                data = progress['ai_mode']
                self.level_manager.level = data['current_level']
                self.level_manager.score = data['score']
                self.level_manager.grid_size = data['grid_size']
                self.level_manager.current_theme = data['theme'] if data['theme'] != "default" else None
                self.ai_player.difficulty = data['ai_difficulty']
                self.theme_var.set(data['theme'])
                self.start_ai_game()
                return True
                
            return False
        except Exception as e:
            print(f"Error loading game state: {e}")
            return False
    
    def start_level(self):
        """Start level with word management improvements"""
        self.level_start_time = time.time()
        
        if self.game_mode == 'single' or self.game_mode == 'ai':
            grid = self.level_manager.start_level()
        elif self.game_mode == 'two_player':
            grid = self.two_player_game.start_level()
            
        self.current_grid = grid
        self.create_grid(grid.grid)
        self.update_display()
        
        # Reset word entry
        self.word_entry.delete(0, tk.END)
        
        return grid
    
    def start_two_player_level(self):
        grid = self.two_player_game.start_level()
        self.current_grid = grid  # Store the grid
        self.create_grid(grid.grid)
        self.update_display(
            self.two_player_game.level,
            self.two_player_game.scores,
            grid.placed_words,
            self.two_player_game.current_player
        )
    
    def start_ai_game(self):
        # self.ai_turn = False
        # self.level_manager.score = 0  # Reset human score
        # self.ai_player.score = 0      # Reset AI score
        self.start_level()
    
    def check_word(self):
        guess = self.word_entry.get().strip().upper()
        self.clear_selection()
        
        if not guess:
            return
            
        if self.game_mode == 'single':
            self._check_single_player_word(guess)
        elif self.game_mode == 'two_player':
            self._check_two_player_word(guess)
        elif self.game_mode == 'ai':
            self._check_ai_game_word(guess)
            
        self.save_progress()
    
    def _check_single_player_word(self, guess):
        grid = self.level_manager.current_grid
        if guess in grid.placed_words:
            grid.placed_words.remove(guess)
            self.level_manager.score += len(guess) * 10
            self.highlight_word(guess, grid.word_paths[guess])
            
            if not grid.placed_words:
                # Calculate time taken
                self.level_time = time.time() - self.level_start_time
                minutes = int(self.level_time // 60)
                seconds = int(self.level_time % 60)
                time_str = f"{minutes:02d}:{seconds:02d}"
                
                if self.level_manager.level_complete():
                    self.show_message(
                        "Congratulations Level Complete!", 
                        f"Time: {time_str}\nBonus: {self.level_manager.grid_size * 20} points!\nTotal Score: {self.level_manager.score}"
                    )
                    self.start_level()
                else:
                    self.show_message(
                        "Game Complete!", 
                        f"Final Time: {time_str}\nFinal Score: {self.level_manager.score}"
                    )
                    self.controller.show_frame(StartPage)
        
        self.update_display(
            self.level_manager.level,
            self.level_manager.score,
            grid.placed_words
        )
    
    def _check_two_player_word(self, guess):
        current_player = self.two_player_game.current_player
        grid = self.two_player_game.current_grid
        
        if self.two_player_game.make_move(current_player, guess):
            self.highlight_word(guess, grid.word_paths[guess], current_player)
            
            if not grid.placed_words:
                # Calculate time taken
                self.level_time = time.time() - self.level_start_time
                minutes = int(self.level_time // 60)
                seconds = int(self.level_time % 60)
                time_str = f"{minutes:02d}:{seconds:02d}"
                
                if self.two_player_game.level_complete():
                    self.show_message(
                       "Congratulations Level Complete!",
                        f"Time: {time_str}\nPlayer 1: {self.two_player_game.scores[1]} | Player 2: {self.two_player_game.scores[2]}"
                    )
                    self.start_two_player_level()
                else:
                    winner = 1 if self.two_player_game.scores[1] > self.two_player_game.scores[2] else 2
                    self.show_message(
                        "Game Complete!",
                        f"Final Time: {time_str}\nPlayer {winner} wins!\nFinal Scores:\nPlayer 1: {self.two_player_game.scores[1]}\nPlayer 2: {self.two_player_game.scores[2]}"
                    )
                    self.controller.show_frame(StartPage)
        
        self.update_display(
            self.two_player_game.level,
            self.two_player_game.scores,
            grid.placed_words,
            self.two_player_game.current_player
        )
        
    def _check_ai_game_word(self, guess):
        """Check human player's word in AI vs Human mode"""
        grid = self.level_manager.current_grid
        if guess in grid.placed_words:
            grid.placed_words.remove(guess)
            self.level_manager.score += len(guess) * 10  # Human gets points
            self.highlight_word(guess, grid.word_paths[guess])
            
            if not grid.placed_words:
                self.handle_level_completion()
            else:
                # Switch to AI's turn after a delay
                self.ai_turn = True
                self.after(500, self.ai_make_move)  # AI moves after 1.5 seconds
        
        self.update_scores()
    
    def update_scores(self):
        """Update score display for AI vs Human mode"""
        self.score_label.config(
            text=f"Human: {self.level_manager.score} | AI: {self.ai_player.score}"
        )
    
    def ai_make_move(self):
        """Handle AI's turn to find a word"""
        if not self.ai_turn or self.game_mode != 'ai':
            return
            
        grid = self.level_manager.current_grid
        if not grid.placed_words:
            return
            
        # Adjust difficulty based on current level
        self.ai_player.adjust_difficulty(self.level_manager.level)
        
        # Get AI's word choice
        ai_guess = self.ai_player.make_move(grid)
        
        if ai_guess and ai_guess in grid.placed_words:
            # Remove found word and update score
            grid.placed_words.remove(ai_guess)
            
            self.ai_player.score += len(ai_guess) * 10
            self.highlight_word(ai_guess, grid.word_paths[ai_guess])
            
            # Show what word AI found
            self.show_message("AI Found", f"The AI found: {ai_guess}")
            
            # Check if level/game is complete
            if not grid.placed_words:
                self.handle_level_completion()
        
        # Switch back to human player
        self.ai_turn = False
        self.update_scores()
    
    def give_hint(self):
        if self.game_mode == 'single':
            grid = self.level_manager.current_grid
        elif self.game_mode == 'two_player':
            grid = self.two_player_game.current_grid
        elif self.game_mode == 'ai':
            grid = self.level_manager.current_grid
            if self.ai_turn:
                return
        
        if not grid.placed_words:
            self.show_message("Hint", "No words left to find!")
            return
            
        word = random.choice(grid.placed_words)
        hint = f"Look for a {len(word)}-letter word: {word[0]}...{word[-1]}"
        
        if self.level_manager.level > 5:
            similar = self.word_bank.get_similar_words(word)
            if similar:
                hint += f"\nRelated: {', '.join(similar[:2])}"
        
        self.show_message("Hint", hint)
    
    def get_level(self):
        if self.game_mode == 'single' or self.game_mode == 'ai':
            return self.level_manager.level
        elif self.game_mode == 'two_player':
            return self.two_player_game.level
    
    def get_score(self):
        if self.game_mode == 'single' or self.game_mode == 'ai':
            return self.level_manager.score
        elif self.game_mode == 'two_player':
            return self.two_player_game.scores
    
    def get_grid_cell(self, row, col):
        if self.game_mode == 'single' or self.game_mode == 'ai':
            return self.level_manager.current_grid.grid[row][col]
        elif self.game_mode == 'two_player':
            return self.two_player_game.current_grid.grid[row][col]

    
if __name__ == "__main__":
    app = App()
    app.title("Word Hunt Challenge")
    app.geometry("1000x700")
    app.mainloop()
